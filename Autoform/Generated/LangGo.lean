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
set_option maxRecDepth 8664

/-!
# LangGo — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `envconfig<clinit>`  (from `envconfig`) -/
def f_envconfig_clinit_ : Func :=
  { name := "envconfig<clinit>"
  , params := []
  , body := (.seq
            (.setField (.name "envconfig") "textUnmarshalerType" (.call "Elem" []))
            (.seq
              (.setField (.name "envconfig") "DefaultTableFormat" (.hole "lit:unquoted"))
              (.seq
                (.setField (.name "envconfig") "lookupEnv" (.field (.name "os") "LookupEnv"))
                (.seq
                  (.setField (.name "envconfig") "lookupEnv" (.field (.name "syscall") "Getenv"))
                  (.seq
                    (.setField
                      (.name "envconfig")
                      "gatherRegexp"
                      (.call "MustCompile" [(.lit (.str "([^A-Z]+|[A-Z]+[^A-Z]+|[A-Z]+)"))]))
                    (.seq
                      (.setField (.name "envconfig") "binaryUnmarshalerType" (.call "Elem" []))
                      (.seq
                        (.setField (.name "envconfig") "DefaultListFormat" (.hole "lit:unquoted"))
                        (.seq
                          (.setField
                            (.name "envconfig")
                            "ErrInvalidSpecification"
                            (.call "New" [(.lit (.str "specification must be a struct pointer"))]))
                          (.seq
                            (.setField (.name "envconfig") "setterType" (.call "Elem" []))
                            (.seq
                              (.setField (.name "envconfig") "decoderType" (.call "Elem" []))
                              (.setField
                                (.name "envconfig")
                                "acronymRegexp"
                                (.call "MustCompile" [(.lit (.str "([A-Z]+)([A-Z][^A-Z]+)"))])))))))))))) }

/-- `env_os.go:envconfig.env_os.go`  (from `env_os.go`) -/
def f_env_os_go_envconfig_env_os_go : Func :=
  { name := "env_os.go:envconfig.env_os.go"
  , params := []
  , body := (.hole "stmt:IMPORT") }

/-- `env_syscall.go:envconfig.env_syscall.go`  (from `env_syscall.go`) -/
def f_env_syscall_go_envconfig_env_syscall_go : Func :=
  { name := "env_syscall.go:envconfig.env_syscall.go"
  , params := []
  , body := (.hole "stmt:IMPORT") }

/-- `envconfig.ParseError.Error`  (from `envconfig.go`) -/
def f_envconfig_ParseError_Error : Func :=
  { name := "envconfig.ParseError.Error"
  , params := ["e"]
  , body := (.ret
            (.call
              "Sprintf"
              [ (.lit
                  (.str "envconfig.Process: assigning %[1]s to %[2]s: converting '%[3]s' to type %[4]s. details: %[5]s"))
              , (.field (.name "e") "KeyName")
              , (.field (.name "e") "FieldName")
              , (.field (.name "e") "Value")
              , (.field (.name "e") "TypeName")
              , (.field (.name "e") "Err") ])) }

/-- `envconfig.gatherInfo`  (from `envconfig.go`) -/
def f_envconfig_gatherInfo : Func :=
  { name := "envconfig.gatherInfo"
  , params := ["prefix", "spec"]
  , body := (.seq
            .skip
            (.seq
              (.assign "s" (.call "ValueOf" [(.name "spec")]))
              (.seq
                .skip
                (.seq
                  (.ifte
                    (.binop "!=" (.call "Kind" []) (.field (.name "reflect") "Ptr"))
                    (.ret (.name "nil"))
                    .skip)
                  (.seq
                    (.assign "s" (.call "Elem" []))
                    (.seq
                      .skip
                      (.seq
                        (.ifte
                          (.binop "!=" (.call "Kind" []) (.field (.name "reflect") "Struct"))
                          (.ret (.name "nil"))
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.assign "typeOfSpec" (.call "Type" []))
                            (.seq
                              .skip
                              (.seq
                                (.assign
                                  "infos"
                                  (.call "make" [(.lit (.int 0)), (.call "NumField" [])]))
                                (.seq (.hole "control:FOR") (.ret (.name "infos")))))))))))))) }

/-- `envconfig.CheckDisallowed`  (from `envconfig.go`) -/
def f_envconfig_CheckDisallowed : Func :=
  { name := "envconfig.CheckDisallowed"
  , params := ["prefix", "spec"]
  , body := (.seq
            .skip
            (.seq
              (.assign "infos" (.call "envconfig.gatherInfo" [(.name "prefix"), (.name "spec")]))
              (.seq
                .skip
                (.seq
                  (.ifte (.binop "!=" (.name "err") (.name "nil")) (.ret (.name "err")) .skip)
                  (.seq
                    .skip
                    (.seq
                      (.assign "vars" (.call "make" [(.hole "lit:unquoted")]))
                      (.seq
                        (.hole "control:FOR")
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.binop "!=" (.name "prefix") (.lit (.str "")))
                              (.assign
                                "prefix"
                                (.binop "+" (.call "ToUpper" [(.name "prefix")]) (.lit (.str "_"))))
                              .skip)
                            (.seq (.hole "control:FOR") (.ret (.name "nil")))))))))))) }

/-- `envconfig.Process`  (from `envconfig.go`) -/
def f_envconfig_Process : Func :=
  { name := "envconfig.Process"
  , params := ["prefix", "spec"]
  , body := (.seq
            .skip
            (.seq
              (.assign "infos" (.call "envconfig.gatherInfo" [(.name "prefix"), (.name "spec")]))
              (.seq (.hole "control:FOR") (.ret (.name "err"))))) }

/-- `envconfig.MustProcess`  (from `envconfig.go`) -/
def f_envconfig_MustProcess : Func :=
  { name := "envconfig.MustProcess"
  , params := ["prefix", "spec"]
  , body := (.seq
            (.seq
              .skip
              (.assign "err" (.call "envconfig.Process" [(.name "prefix"), (.name "spec")])))
            (.ifte
              (.binop "!=" (.name "err") (.name "nil"))
              (.expr (.call "panic" [(.name "err")]))
              .skip)) }

/-- `envconfig.processField`  (from `envconfig.go`) -/
def f_envconfig_processField : Func :=
  { name := "envconfig.processField"
  , params := ["value", "field"]
  , body := (.seq
            .skip
            (.seq
              (.assign "typ" (.call "Type" []))
              (.seq
                .skip
                (.seq
                  (.assign "decoder" (.call "envconfig.decoderFrom" [(.name "field")]))
                  (.seq
                    .skip
                    (.seq
                      (.ifte
                        (.binop "!=" (.name "decoder") (.name "nil"))
                        (.ret (.call "Decode" [(.name "value")]))
                        .skip)
                      (.seq
                        .skip
                        (.seq
                          (.assign "setter" (.call "envconfig.setterFrom" [(.name "field")]))
                          (.seq
                            .skip
                            (.seq
                              (.ifte
                                (.binop "!=" (.name "setter") (.name "nil"))
                                (.ret (.call "Set" [(.name "value")]))
                                .skip)
                              (.seq
                                (.seq
                                  .skip
                                  (.assign
                                    "t"
                                    (.call "envconfig.textUnmarshaler" [(.name "field")])))
                                (.seq
                                  (.ifte
                                    (.binop "!=" (.name "t") (.name "nil"))
                                    (.ret (.call "UnmarshalText" [(.hole "call:no-callee-name")]))
                                    .skip)
                                  (.seq
                                    (.seq
                                      .skip
                                      (.assign
                                        "b"
                                        (.call "envconfig.binaryUnmarshaler" [(.name "field")])))
                                    (.seq
                                      (.ifte
                                        (.binop "!=" (.name "b") (.name "nil"))
                                        (.ret
                                        (.call "UnmarshalBinary" [(.hole "call:no-callee-name")]))
                                        .skip)
                                      (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.call "Kind" [])
                                        (.field (.name "reflect") "Ptr"))
                                        (.seq
                                        (.assign "typ" (.call "Elem" []))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.call "IsNil" [])
                                        (.expr (.call "Set" [(.call "New" [(.name "typ")])]))
                                        .skip)
                                        (.assign "field" (.call "Elem" [])))))
                                        .skip)
                                        (.seq (.hole "control:SWITCH") (.ret (.name "nil"))))))))))))))))))) }

/-- `envconfig.interfaceFrom`  (from `envconfig.go`) -/
def f_envconfig_interfaceFrom : Func :=
  { name := "envconfig.interfaceFrom"
  , params := ["field", "fn"]
  , body := (.seq
            .skip
            (.seq
              (.ifte (.unop "!" (.call "CanInterface" [])) (.ret (.lit .unit)) .skip)
              (.seq
                .skip
                (.seq
                  (.expr (.name "ok"))
                  (.seq
                    (.expr (.call "fn" [(.call "Interface" []), (.hole "op:addressOf")]))
                    (.seq
                      .skip
                      (.ifte
                        (.binop "&&" (.unop "!" (.name "ok")) (.call "CanAddr" []))
                        (.expr (.call "fn" [(.call "Interface" []), (.hole "op:addressOf")]))
                        .skip))))))) }

/-- `envconfig.decoderFrom.<lambda>0`  (from `envconfig.go`) -/
def f_envconfig_decoderFrom__lambda_0 : Func :=
  { name := "envconfig.decoderFrom.<lambda>0"
  , params := ["v", "ok"]
  , body := (.hole "assign:arity") }

/-- `envconfig.decoderFrom`  (from `envconfig.go`) -/
def f_envconfig_decoderFrom : Func :=
  { name := "envconfig.decoderFrom"
  , params := ["field"]
  , body := (.seq
            (.expr
              (.call
                "envconfig.interfaceFrom"
                [(.name "field"), (.fnref "envconfig.decoderFrom.<lambda>0")]))
            (.ret (.name "d"))) }

/-- `envconfig.setterFrom.<lambda>1`  (from `envconfig.go`) -/
def f_envconfig_setterFrom__lambda_1 : Func :=
  { name := "envconfig.setterFrom.<lambda>1"
  , params := ["v", "ok"]
  , body := (.hole "assign:arity") }

/-- `envconfig.setterFrom`  (from `envconfig.go`) -/
def f_envconfig_setterFrom : Func :=
  { name := "envconfig.setterFrom"
  , params := ["field"]
  , body := (.seq
            (.expr
              (.call
                "envconfig.interfaceFrom"
                [(.name "field"), (.fnref "envconfig.setterFrom.<lambda>1")]))
            (.ret (.name "s"))) }

/-- `envconfig.textUnmarshaler.<lambda>2`  (from `envconfig.go`) -/
def f_envconfig_textUnmarshaler__lambda_2 : Func :=
  { name := "envconfig.textUnmarshaler.<lambda>2"
  , params := ["v", "ok"]
  , body := (.hole "assign:arity") }

/-- `envconfig.textUnmarshaler`  (from `envconfig.go`) -/
def f_envconfig_textUnmarshaler : Func :=
  { name := "envconfig.textUnmarshaler"
  , params := ["field"]
  , body := (.seq
            (.expr
              (.call
                "envconfig.interfaceFrom"
                [(.name "field"), (.fnref "envconfig.textUnmarshaler.<lambda>2")]))
            (.ret (.name "t"))) }

/-- `envconfig.binaryUnmarshaler.<lambda>3`  (from `envconfig.go`) -/
def f_envconfig_binaryUnmarshaler__lambda_3 : Func :=
  { name := "envconfig.binaryUnmarshaler.<lambda>3"
  , params := ["v", "ok"]
  , body := (.hole "assign:arity") }

/-- `envconfig.binaryUnmarshaler`  (from `envconfig.go`) -/
def f_envconfig_binaryUnmarshaler : Func :=
  { name := "envconfig.binaryUnmarshaler"
  , params := ["field"]
  , body := (.seq
            (.expr
              (.call
                "envconfig.interfaceFrom"
                [(.name "field"), (.fnref "envconfig.binaryUnmarshaler.<lambda>3")]))
            (.ret (.name "b"))) }

/-- `envconfig.isTrue`  (from `envconfig.go`) -/
def f_envconfig_isTrue : Func :=
  { name := "envconfig.isTrue"
  , params := ["s"]
  , body := (.seq .skip (.seq (.assign "b" (.call "ParseBool" [(.name "s")])) (.ret (.name "b")))) }

/-- `envconfig.go:envconfig.envconfig.go`  (from `envconfig.go`) -/
def f_envconfig_go_envconfig_envconfig_go : Func :=
  { name := "envconfig.go:envconfig.envconfig.go"
  , params := []
  , body := (.seq
            (.hole "stmt:IMPORT")
            (.seq
              (.hole "stmt:IMPORT")
              (.seq
                (.hole "stmt:IMPORT")
                (.seq
                  (.hole "stmt:IMPORT")
                  (.seq
                    (.hole "stmt:IMPORT")
                    (.seq
                      (.hole "stmt:IMPORT")
                      (.seq
                        (.hole "stmt:IMPORT")
                        (.seq
                          (.hole "stmt:IMPORT")
                          (.seq
                            (.hole "stmt:IMPORT")
                            (.seq
                              (.hole "stmt:TYPE_DECL")
                              (.seq
                                (.hole "stmt:TYPE_DECL")
                                (.seq (.hole "stmt:TYPE_DECL") (.hole "stmt:TYPE_DECL"))))))))))))) }

/-- `envconfig.TestParseURL`  (from `envconfig_1.8_test.go`) -/
def f_envconfig_TestParseURL : Func :=
  { name := "envconfig.TestParseURL"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call
                      "Setenv"
                      [ (.lit (.str "ENV_CONFIG_URLVALUE"))
                      , (.lit (.str "https://github.com/kelseyhightower/envconfig")) ]))
                  (.seq
                    (.expr
                      (.call
                        "Setenv"
                        [ (.lit (.str "ENV_CONFIG_URLPOINTER"))
                        , (.lit (.str "https://github.com/kelseyhightower/envconfig")) ]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "err"
                          (.call
                            "envconfig.Process"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.binop "!=" (.name "err") (.name "nil"))
                              (.expr
                                (.call "Fatal" [(.lit (.str "unexpected error:")), (.name "err")]))
                              .skip)
                            (.seq
                              .skip
                              (.seq
                                (.assign
                                  "u"
                                  (.call
                                    "Parse"
                                    [(.lit (.str "https://github.com/kelseyhightower/envconfig"))]))
                                (.seq
                                  .skip
                                  (.seq
                                    (.ifte
                                      (.binop "!=" (.name "err") (.name "nil"))
                                      (.expr
                                        (.call
                                        "Fatalf"
                                        [(.lit (.str "unexpected error: %v")), (.name "err")]))
                                      .skip)
                                    (.seq
                                      .skip
                                      (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "UrlValue")
                                        (.hole "op:indirection"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %q, got %q"))
                                        , (.name "u")
                                        , (.mcall (.name "s") "UrlValue" []) ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.hole "op:indirection")
                                        (.hole "op:indirection"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %q, got %q"))
                                        , (.name "u")
                                        , (.field (.name "s") "UrlPointer") ]))
                                        .skip))))))))))))))))) }

/-- `envconfig.TestParseURLError`  (from `envconfig_1.8_test.go`) -/
def f_envconfig_TestParseURLError : Func :=
  { name := "envconfig.TestParseURLError"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call
                      "Setenv"
                      [(.lit (.str "ENV_CONFIG_URLPOINTER")), (.lit (.str "http_://foo"))]))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "err"
                        (.call
                          "envconfig.Process"
                          [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                      (.seq
                        .skip
                        (.seq
                          (.assign "v" (.name "err"))
                          (.seq
                            .skip
                            (.seq
                              (.ifte
                                (.unop "!" (.name "ok"))
                                (.expr
                                  (.call
                                    "Fatalf"
                                    [ (.lit (.str "expected ParseError, got %T %v"))
                                    , (.name "err")
                                    , (.name "err") ]))
                                .skip)
                              (.seq
                                .skip
                                (.seq
                                  (.ifte
                                    (.binop
                                      "!="
                                      (.field (.name "v") "FieldName")
                                      (.lit (.str "UrlPointer")))
                                    (.expr
                                      (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %v"))
                                        , (.lit (.str "UrlPointer"))
                                        , (.field (.name "v") "FieldName") ]))
                                    .skip)
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign
                                        "expectedUnerlyingError"
                                        (.call
                                        "Error"
                                        [ (.lit (.str "parse"))
                                        , (.lit (.str "http_://foo"))
                                        , (.call
                                        "New"
                                        [ (.lit
                                        (.str "first path segment in URL cannot contain colon")) ]) ]))
                                      (.seq
                                        .skip
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.mcall (.name "v") "Err" [])
                                        (.call "Error" []))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %q, got %q"))
                                        , (.name "expectedUnerlyingError")
                                        , (.field (.name "v") "Err") ]))
                                        .skip)))))))))))))))) }

/-- `envconfig_1.8_test.go:envconfig.envconfig_1.8_test.go`  (from `envconfig_1.8_test.go`) -/
def f_envconfig_1_8_test_go_envconfig_envconfig_1_8_test_go : Func :=
  { name := "envconfig_1.8_test.go:envconfig.envconfig_1.8_test.go"
  , params := []
  , body := (.seq
            (.hole "stmt:IMPORT")
            (.seq
              (.hole "stmt:IMPORT")
              (.seq (.hole "stmt:IMPORT") (.seq (.hole "stmt:IMPORT") (.hole "stmt:TYPE_DECL"))))) }

/-- `envconfig.HonorDecodeInStruct.Decode`  (from `envconfig_test.go`) -/
def f_envconfig_HonorDecodeInStruct_Decode : Func :=
  { name := "envconfig.HonorDecodeInStruct.Decode"
  , params := ["h", "env"]
  , body := (.seq (.setField (.name "h") "Value" (.lit (.str "decoded"))) (.ret (.name "nil"))) }

/-- `envconfig.CustomURL.UnmarshalBinary`  (from `envconfig_test.go`) -/
def f_envconfig_CustomURL_UnmarshalBinary : Func :=
  { name := "envconfig.CustomURL.UnmarshalBinary"
  , params := ["cu", "data"]
  , body := (.seq
            .skip
            (.seq
              (.assign "u" (.call "Parse" [(.call "string" [(.name "data")])]))
              (.seq (.setField (.name "cu") "Value" (.name "u")) (.ret (.name "err"))))) }

/-- `envconfig.TestProcess`  (from `envconfig_test.go`) -/
def f_envconfig_TestProcess : Func :=
  { name := "envconfig.TestProcess"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_DEBUG")), (.lit (.str "true"))]))
                  (.seq
                    (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_PORT")), (.lit (.str "8080"))]))
                    (.seq
                      (.expr
                        (.call "Setenv" [(.lit (.str "ENV_CONFIG_RATE")), (.lit (.str "0.5"))]))
                      (.seq
                        (.expr
                          (.call "Setenv" [(.lit (.str "ENV_CONFIG_USER")), (.lit (.str "Kelsey"))]))
                        (.seq
                          (.expr
                            (.call
                              "Setenv"
                              [(.lit (.str "ENV_CONFIG_TIMEOUT")), (.lit (.str "2m"))]))
                          (.seq
                            (.expr
                              (.call
                                "Setenv"
                                [ (.lit (.str "ENV_CONFIG_ADMINUSERS"))
                                , (.lit (.str "John,Adam,Will")) ]))
                            (.seq
                              (.expr
                                (.call
                                  "Setenv"
                                  [(.lit (.str "ENV_CONFIG_MAGICNUMBERS")), (.lit (.str "5,10,20"))]))
                              (.seq
                                (.expr
                                  (.call
                                    "Setenv"
                                    [(.lit (.str "ENV_CONFIG_EMPTYNUMBERS")), (.lit (.str ""))]))
                                (.seq
                                  (.expr
                                    (.call
                                      "Setenv"
                                      [ (.lit (.str "ENV_CONFIG_BYTESLICE"))
                                      , (.lit (.str "this is a test value")) ]))
                                  (.seq
                                    (.expr
                                      (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_COLORCODES"))
                                        , (.lit (.str "red:1,green:2,blue:3")) ]))
                                    (.seq
                                      (.expr
                                        (.call
                                        "Setenv"
                                        [(.lit (.str "SERVICE_HOST")), (.lit (.str "127.0.0.1"))]))
                                      (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [(.lit (.str "ENV_CONFIG_TTL")), (.lit (.str "30"))]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_REQUIREDVAR"))
                                        , (.lit (.str "foo")) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_IGNORED"))
                                        , (.lit (.str "was-not-ignored")) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_OUTER_INNER"))
                                        , (.lit (.str "iamnested")) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_AFTERNESTED"))
                                        , (.lit (.str "after")) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [(.lit (.str "ENV_CONFIG_HONOR")), (.lit (.str "honor"))]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_DATETIME"))
                                        , (.lit (.str "2016-08-16T18:57:05Z")) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_MULTI_WORD_VAR_WITH_AUTO_SPLIT"))
                                        , (.lit (.str "24")) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_MULTI_WORD_ACR_WITH_AUTO_SPLIT"))
                                        , (.lit (.str "25")) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_URLVALUE"))
                                        , (.lit (.str "https://github.com/kelseyhightower/envconfig")) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_URLPOINTER"))
                                        , (.lit (.str "https://github.com/kelseyhightower/envconfig")) ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "err"
                                        (.call
                                        "envconfig.Process"
                                        [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "err") (.name "nil"))
                                        (.expr (.call "Error" [(.call "Error" [])]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "NoPrefixWithAlt")
                                        (.lit (.str "127.0.0.1")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %v, got %v"))
                                        , (.lit (.str "127.0.0.1"))
                                        , (.field (.name "s") "NoPrefixWithAlt") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.unop "!" (.field (.name "s") "Debug"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %v, got %v"))
                                        , (.name "true")
                                        , (.field (.name "s") "Debug") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.field (.name "s") "Port") (.lit (.int 8080)))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %d, got %v"))
                                        , (.lit (.int 8080))
                                        , (.field (.name "s") "Port") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "Rate")
                                        (.hole "lit:float"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %f, got %v"))
                                        , (.hole "lit:float")
                                        , (.field (.name "s") "Rate") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.field (.name "s") "TTL") (.lit (.int 30)))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %d, got %v"))
                                        , (.lit (.int 30))
                                        , (.field (.name "s") "TTL") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "User")
                                        (.lit (.str "Kelsey")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %s"))
                                        , (.lit (.str "Kelsey"))
                                        , (.field (.name "s") "User") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "Timeout")
                                        (.binop
                                        "*"
                                        (.lit (.int 2))
                                        (.field (.name "time") "Minute")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %s"))
                                        , (.binop
                                        "*"
                                        (.lit (.int 2))
                                        (.field (.name "time") "Minute"))
                                        , (.field (.name "s") "Timeout") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "RequiredVar")
                                        (.lit (.str "foo")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %s"))
                                        , (.lit (.str "foo"))
                                        , (.field (.name "s") "RequiredVar") ]))
                                        .skip)
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
                                        (.binop
                                        "!="
                                        (.mcall
                                        (.name "s")
                                        "AdminUsers"
                                        [(.field (.name "s") "AdminUsers")])
                                        (.lit (.int 3)))
                                        (.binop
                                        "!="
                                        (.index (.field (.name "s") "AdminUsers") (.lit (.int 0)))
                                        (.lit (.str "John"))))
                                        (.binop
                                        "!="
                                        (.index (.field (.name "s") "AdminUsers") (.lit (.int 1)))
                                        (.lit (.str "Adam"))))
                                        (.binop
                                        "!="
                                        (.index (.field (.name "s") "AdminUsers") (.lit (.int 2)))
                                        (.lit (.str "Will"))))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %#v, got %#v"))
                                        , (.hole "op:arrayInitializer")
                                        , (.field (.name "s") "AdminUsers") ]))
                                        .skip)
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
                                        (.binop
                                        "!="
                                        (.mcall
                                        (.name "s")
                                        "MagicNumbers"
                                        [(.field (.name "s") "MagicNumbers")])
                                        (.lit (.int 3)))
                                        (.binop
                                        "!="
                                        (.index (.field (.name "s") "MagicNumbers") (.lit (.int 0)))
                                        (.lit (.int 5))))
                                        (.binop
                                        "!="
                                        (.index (.field (.name "s") "MagicNumbers") (.lit (.int 1)))
                                        (.lit (.int 10))))
                                        (.binop
                                        "!="
                                        (.index (.field (.name "s") "MagicNumbers") (.lit (.int 2)))
                                        (.lit (.int 20))))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %#v, got %#v"))
                                        , (.hole "op:arrayInitializer")
                                        , (.field (.name "s") "MagicNumbers") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.mcall
                                        (.name "s")
                                        "EmptyNumbers"
                                        [(.field (.name "s") "EmptyNumbers")])
                                        (.lit (.int 0)))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %#v, got %#v"))
                                        , (.hole "op:arrayInitializer")
                                        , (.field (.name "s") "EmptyNumbers") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "expected" (.lit (.str "this is a test value")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.mcall
                                        (.name "s")
                                        "ByteSlice"
                                        [(.field (.name "s") "ByteSlice")])
                                        (.name "expected"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %v, got %v"))
                                        , (.name "expected")
                                        , (.mcall
                                        (.name "s")
                                        "ByteSlice"
                                        [(.field (.name "s") "ByteSlice")]) ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "Ignored")
                                        (.lit (.str "")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected empty string, got %#v"))
                                        , (.field (.name "s") "Ignored") ]))
                                        .skip)
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
                                        (.binop
                                        "!="
                                        (.mcall
                                        (.name "s")
                                        "ColorCodes"
                                        [(.field (.name "s") "ColorCodes")])
                                        (.lit (.int 3)))
                                        (.binop
                                        "!="
                                        (.index
                                        (.field (.name "s") "ColorCodes")
                                        (.lit (.str "red")))
                                        (.lit (.int 1))))
                                        (.binop
                                        "!="
                                        (.index
                                        (.field (.name "s") "ColorCodes")
                                        (.lit (.str "green")))
                                        (.lit (.int 2))))
                                        (.binop
                                        "!="
                                        (.index
                                        (.field (.name "s") "ColorCodes")
                                        (.lit (.str "blue")))
                                        (.lit (.int 3))))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %#v, got %#v"))
                                        , (.field (.name "s") "ColorCodes") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field
                                        (.field (.name "s") "NestedSpecification")
                                        "Property")
                                        (.lit (.str "iamnested")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected '%s' string, got %#v"))
                                        , (.lit (.str "iamnested"))
                                        , (.field
                                        (.field (.name "s") "NestedSpecification")
                                        "Property") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field
                                        (.field (.name "s") "NestedSpecification")
                                        "PropertyWithDefault")
                                        (.lit (.str "fuzzybydefault")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected default '%s' string, got %#v"))
                                        , (.lit (.str "fuzzybydefault"))
                                        , (.field
                                        (.field (.name "s") "NestedSpecification")
                                        "PropertyWithDefault") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "AfterNested")
                                        (.lit (.str "after")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected default '%s' string, got %#v"))
                                        , (.lit (.str "after"))
                                        , (.field (.name "s") "AfterNested") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.field (.name "s") "DecodeStruct") "Value")
                                        (.lit (.str "decoded")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected default '%s' string, got %#v"))
                                        , (.lit (.str "decoded"))
                                        , (.field (.field (.name "s") "DecodeStruct") "Value") ]))
                                        .skip)
                                        (.seq
                                        (.seq
                                        .skip
                                        (.assign
                                        "expected"
                                        (.call
                                        "Date"
                                        [ (.lit (.int 2016))
                                        , (.lit (.int 8))
                                        , (.lit (.int 16))
                                        , (.lit (.int 18))
                                        , (.lit (.int 57))
                                        , (.lit (.int 5))
                                        , (.lit (.int 0))
                                        , (.field (.name "time") "UTC") ])))
                                        (.seq
                                        (.ifte
                                        (.unop
                                        "!"
                                        (.mcall (.name "s") "Datetime" [(.name "expected")]))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %s"))
                                        , (.call "Format" [(.field (.name "time") "RFC3339")])
                                        , (.mcall
                                        (.name "s")
                                        "Datetime"
                                        [(.field (.name "time") "RFC3339")]) ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "MultiWordVarWithAutoSplit")
                                        (.lit (.int 24)))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %q, got %q"))
                                        , (.lit (.int 24))
                                        , (.field (.name "s") "MultiWordVarWithAutoSplit") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "MultiWordACRWithAutoSplit")
                                        (.lit (.int 25)))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %d, got %d"))
                                        , (.lit (.int 25))
                                        , (.field (.name "s") "MultiWordACRWithAutoSplit") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "u"
                                        (.call
                                        "Parse"
                                        [ (.lit (.str "https://github.com/kelseyhightower/envconfig")) ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "err") (.name "nil"))
                                        (.expr
                                        (.call
                                        "Fatalf"
                                        [(.lit (.str "unexpected error: %v")), (.name "err")]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.hole "op:indirection")
                                        (.hole "op:indirection"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %q, got %q"))
                                        , (.name "u")
                                        , (.mcall (.field (.name "s") "UrlValue") "Value" []) ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.hole "op:indirection")
                                        (.hole "op:indirection"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %q, got %q"))
                                        , (.name "u")
                                        , (.mcall (.field (.name "s") "UrlPointer") "Value" []) ]))
                                        .skip))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- `envconfig.TestParseErrorBool`  (from `envconfig_test.go`) -/
def f_envconfig_TestParseErrorBool : Func :=
  { name := "envconfig.TestParseErrorBool"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call "Setenv" [(.lit (.str "ENV_CONFIG_DEBUG")), (.lit (.str "string"))]))
                  (.seq
                    (.expr
                      (.call "Setenv" [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "err"
                          (.call
                            "envconfig.Process"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                        (.seq
                          .skip
                          (.seq
                            (.assign "v" (.name "err"))
                            (.seq
                              .skip
                              (.seq
                                (.ifte
                                  (.unop "!" (.name "ok"))
                                  (.expr
                                    (.call
                                      "Errorf"
                                      [(.lit (.str "expected ParseError, got %v")), (.name "v")]))
                                  .skip)
                                (.seq
                                  .skip
                                  (.seq
                                    (.ifte
                                      (.binop
                                        "!="
                                        (.field (.name "v") "FieldName")
                                        (.lit (.str "Debug")))
                                      (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %v"))
                                        , (.lit (.str "Debug"))
                                        , (.field (.name "v") "FieldName") ]))
                                      .skip)
                                    (.seq
                                      .skip
                                      (.ifte
                                        (.binop "!=" (.field (.name "s") "Debug") (.name "false"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %v, got %v"))
                                        , (.name "false")
                                        , (.field (.name "s") "Debug") ]))
                                        .skip))))))))))))))) }

/-- `envconfig.TestParseErrorFloat32`  (from `envconfig_test.go`) -/
def f_envconfig_TestParseErrorFloat32 : Func :=
  { name := "envconfig.TestParseErrorFloat32"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_RATE")), (.lit (.str "string"))]))
                  (.seq
                    (.expr
                      (.call "Setenv" [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "err"
                          (.call
                            "envconfig.Process"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                        (.seq
                          .skip
                          (.seq
                            (.assign "v" (.name "err"))
                            (.seq
                              .skip
                              (.seq
                                (.ifte
                                  (.unop "!" (.name "ok"))
                                  (.expr
                                    (.call
                                      "Errorf"
                                      [(.lit (.str "expected ParseError, got %v")), (.name "v")]))
                                  .skip)
                                (.seq
                                  .skip
                                  (.seq
                                    (.ifte
                                      (.binop
                                        "!="
                                        (.field (.name "v") "FieldName")
                                        (.lit (.str "Rate")))
                                      (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %v"))
                                        , (.lit (.str "Rate"))
                                        , (.field (.name "v") "FieldName") ]))
                                      .skip)
                                    (.seq
                                      .skip
                                      (.ifte
                                        (.binop "!=" (.field (.name "s") "Rate") (.lit (.int 0)))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %v, got %v"))
                                        , (.lit (.int 0))
                                        , (.field (.name "s") "Rate") ]))
                                        .skip))))))))))))))) }

/-- `envconfig.TestParseErrorInt`  (from `envconfig_test.go`) -/
def f_envconfig_TestParseErrorInt : Func :=
  { name := "envconfig.TestParseErrorInt"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_PORT")), (.lit (.str "string"))]))
                  (.seq
                    (.expr
                      (.call "Setenv" [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "err"
                          (.call
                            "envconfig.Process"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                        (.seq
                          .skip
                          (.seq
                            (.assign "v" (.name "err"))
                            (.seq
                              .skip
                              (.seq
                                (.ifte
                                  (.unop "!" (.name "ok"))
                                  (.expr
                                    (.call
                                      "Errorf"
                                      [(.lit (.str "expected ParseError, got %v")), (.name "v")]))
                                  .skip)
                                (.seq
                                  .skip
                                  (.seq
                                    (.ifte
                                      (.binop
                                        "!="
                                        (.field (.name "v") "FieldName")
                                        (.lit (.str "Port")))
                                      (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %v"))
                                        , (.lit (.str "Port"))
                                        , (.field (.name "v") "FieldName") ]))
                                      .skip)
                                    (.seq
                                      .skip
                                      (.ifte
                                        (.binop "!=" (.field (.name "s") "Port") (.lit (.int 0)))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %v, got %v"))
                                        , (.lit (.int 0))
                                        , (.field (.name "s") "Port") ]))
                                        .skip))))))))))))))) }

/-- `envconfig.TestParseErrorUint`  (from `envconfig_test.go`) -/
def f_envconfig_TestParseErrorUint : Func :=
  { name := "envconfig.TestParseErrorUint"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_TTL")), (.lit (.str "-30"))]))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "err"
                        (.call
                          "envconfig.Process"
                          [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                      (.seq
                        .skip
                        (.seq
                          (.assign "v" (.name "err"))
                          (.seq
                            .skip
                            (.seq
                              (.ifte
                                (.unop "!" (.name "ok"))
                                (.expr
                                  (.call
                                    "Errorf"
                                    [(.lit (.str "expected ParseError, got %v")), (.name "v")]))
                                .skip)
                              (.seq
                                .skip
                                (.seq
                                  (.ifte
                                    (.binop
                                      "!="
                                      (.field (.name "v") "FieldName")
                                      (.lit (.str "TTL")))
                                    (.expr
                                      (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %v"))
                                        , (.lit (.str "TTL"))
                                        , (.field (.name "v") "FieldName") ]))
                                    .skip)
                                  (.seq
                                    .skip
                                    (.ifte
                                      (.binop "!=" (.field (.name "s") "TTL") (.lit (.int 0)))
                                      (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %v, got %v"))
                                        , (.lit (.int 0))
                                        , (.field (.name "s") "TTL") ]))
                                      .skip)))))))))))))) }

/-- `envconfig.TestParseErrorSplitWords`  (from `envconfig_test.go`) -/
def f_envconfig_TestParseErrorSplitWords : Func :=
  { name := "envconfig.TestParseErrorSplitWords"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call
                      "Setenv"
                      [ (.lit (.str "ENV_CONFIG_MULTI_WORD_VAR_WITH_AUTO_SPLIT"))
                      , (.lit (.str "shakespeare")) ]))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "err"
                        (.call
                          "envconfig.Process"
                          [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                      (.seq
                        .skip
                        (.seq
                          (.assign "v" (.name "err"))
                          (.seq
                            .skip
                            (.seq
                              (.ifte
                                (.unop "!" (.name "ok"))
                                (.expr
                                  (.call
                                    "Errorf"
                                    [(.lit (.str "expected ParseError, got %v")), (.name "v")]))
                                .skip)
                              (.seq
                                .skip
                                (.seq
                                  (.ifte
                                    (.binop
                                      "!="
                                      (.field (.name "v") "FieldName")
                                      (.lit (.str "MultiWordVarWithAutoSplit")))
                                    (.expr
                                      (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %v"))
                                        , (.lit (.str ""))
                                        , (.field (.name "v") "FieldName") ]))
                                    .skip)
                                  (.seq
                                    .skip
                                    (.ifte
                                      (.binop
                                        "!="
                                        (.field (.name "s") "MultiWordVarWithAutoSplit")
                                        (.lit (.int 0)))
                                      (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %v, got %v"))
                                        , (.lit (.int 0))
                                        , (.field (.name "s") "MultiWordVarWithAutoSplit") ]))
                                      .skip)))))))))))))) }

/-- `envconfig.TestErrInvalidSpecification`  (from `envconfig_test.go`) -/
def f_envconfig_TestErrInvalidSpecification : Func :=
  { name := "envconfig.TestErrInvalidSpecification"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.assign "m" (.call "make" [(.hole "lit:unquoted")]))
              (.seq
                .skip
                (.seq
                  (.assign
                    "err"
                    (.call "envconfig.Process" [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                  (.seq
                    .skip
                    (.ifte
                      (.binop
                        "!="
                        (.name "err")
                        (.field (.name "envconfig") "ErrInvalidSpecification"))
                      (.expr
                        (.call
                          "Errorf"
                          [ (.lit (.str "expected %v, got %v"))
                          , (.field (.name "envconfig") "ErrInvalidSpecification")
                          , (.name "err") ]))
                      .skip)))))) }

/-- `envconfig.TestUnsetVars`  (from `envconfig_test.go`) -/
def f_envconfig_TestUnsetVars : Func :=
  { name := "envconfig.TestUnsetVars"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr (.call "Setenv" [(.lit (.str "USER")), (.lit (.str "foo"))]))
                  (.seq
                    (.expr
                      (.call "Setenv" [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                    (.seq
                      (.seq
                        .skip
                        (.assign
                          "err"
                          (.call
                            "envconfig.Process"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                      (.seq
                        (.ifte
                          (.binop "!=" (.name "err") (.name "nil"))
                          (.expr (.call "Error" [(.call "Error" [])]))
                          .skip)
                        (.seq
                          .skip
                          (.ifte
                            (.binop "!=" (.field (.name "s") "User") (.lit (.str "")))
                            (.expr
                              (.call
                                "Errorf"
                                [ (.lit (.str "expected %q, got %q"))
                                , (.lit (.str ""))
                                , (.field (.name "s") "User") ]))
                            .skip))))))))) }

/-- `envconfig.TestAlternateVarNames`  (from `envconfig_test.go`) -/
def f_envconfig_TestAlternateVarNames : Func :=
  { name := "envconfig.TestAlternateVarNames"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call
                      "Setenv"
                      [(.lit (.str "ENV_CONFIG_MULTI_WORD_VAR")), (.lit (.str "foo"))]))
                  (.seq
                    (.expr
                      (.call
                        "Setenv"
                        [(.lit (.str "ENV_CONFIG_MULTI_WORD_VAR_WITH_ALT")), (.lit (.str "bar"))]))
                    (.seq
                      (.expr
                        (.call
                          "Setenv"
                          [ (.lit (.str "ENV_CONFIG_MULTI_WORD_VAR_WITH_LOWER_CASE_ALT"))
                          , (.lit (.str "baz")) ]))
                      (.seq
                        (.expr
                          (.call
                            "Setenv"
                            [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                        (.seq
                          (.seq
                            .skip
                            (.assign
                              "err"
                              (.call
                                "envconfig.Process"
                                [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                          (.seq
                            (.ifte
                              (.binop "!=" (.name "err") (.name "nil"))
                              (.expr (.call "Error" [(.call "Error" [])]))
                              .skip)
                            (.seq
                              .skip
                              (.seq
                                (.ifte
                                  (.binop "!=" (.field (.name "s") "MultiWordVar") (.lit (.str "")))
                                  (.expr
                                    (.call
                                      "Errorf"
                                      [ (.lit (.str "expected %q, got %q"))
                                      , (.lit (.str ""))
                                      , (.field (.name "s") "MultiWordVar") ]))
                                  .skip)
                                (.seq
                                  .skip
                                  (.seq
                                    (.ifte
                                      (.binop
                                        "!="
                                        (.field (.name "s") "MultiWordVarWithAlt")
                                        (.lit (.str "bar")))
                                      (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %q, got %q"))
                                        , (.lit (.str "bar"))
                                        , (.field (.name "s") "MultiWordVarWithAlt") ]))
                                      .skip)
                                    (.seq
                                      .skip
                                      (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "MultiWordVarWithLowerCaseAlt")
                                        (.lit (.str "baz")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %q, got %q"))
                                        , (.lit (.str "baz"))
                                        , (.field (.name "s") "MultiWordVarWithLowerCaseAlt") ]))
                                        .skip))))))))))))))) }

/-- `envconfig.TestRequiredVar`  (from `envconfig_test.go`) -/
def f_envconfig_TestRequiredVar : Func :=
  { name := "envconfig.TestRequiredVar"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call
                      "Setenv"
                      [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foobar"))]))
                  (.seq
                    (.seq
                      .skip
                      (.assign
                        "err"
                        (.call
                          "envconfig.Process"
                          [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                    (.seq
                      (.ifte
                        (.binop "!=" (.name "err") (.name "nil"))
                        (.expr (.call "Error" [(.call "Error" [])]))
                        .skip)
                      (.seq
                        .skip
                        (.ifte
                          (.binop "!=" (.field (.name "s") "RequiredVar") (.lit (.str "foobar")))
                          (.expr
                            (.call
                              "Errorf"
                              [ (.lit (.str "expected %s, got %s"))
                              , (.lit (.str "foobar"))
                              , (.field (.name "s") "RequiredVar") ]))
                          .skip)))))))) }

/-- `envconfig.TestRequiredMissing`  (from `envconfig_test.go`) -/
def f_envconfig_TestRequiredMissing : Func :=
  { name := "envconfig.TestRequiredMissing"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "err"
                      (.call
                        "envconfig.Process"
                        [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                    (.seq
                      .skip
                      (.ifte
                        (.binop "==" (.name "err") (.name "nil"))
                        (.expr
                          (.call
                            "Error"
                            [(.lit (.str "no failure when missing required variable"))]))
                        .skip))))))) }

/-- `envconfig.TestBlankDefaultVar`  (from `envconfig_test.go`) -/
def f_envconfig_TestBlankDefaultVar : Func :=
  { name := "envconfig.TestBlankDefaultVar"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call
                      "Setenv"
                      [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "requiredvalue"))]))
                  (.seq
                    (.seq
                      .skip
                      (.assign
                        "err"
                        (.call
                          "envconfig.Process"
                          [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                    (.seq
                      (.ifte
                        (.binop "!=" (.name "err") (.name "nil"))
                        (.expr (.call "Error" [(.call "Error" [])]))
                        .skip)
                      (.seq
                        .skip
                        (.seq
                          (.ifte
                            (.binop "!=" (.field (.name "s") "DefaultVar") (.lit (.str "foobar")))
                            (.expr
                              (.call
                                "Errorf"
                                [ (.lit (.str "expected %s, got %s"))
                                , (.lit (.str "foobar"))
                                , (.field (.name "s") "DefaultVar") ]))
                            .skip)
                          (.seq
                            .skip
                            (.ifte
                              (.binop "!=" (.hole "op:indirection") (.lit (.str "foo2baz")))
                              (.expr
                                (.call
                                  "Errorf"
                                  [ (.lit (.str "expected %s, got %s"))
                                  , (.lit (.str "foo2baz"))
                                  , (.hole "op:indirection") ]))
                              .skip)))))))))) }

/-- `envconfig.TestNonBlankDefaultVar`  (from `envconfig_test.go`) -/
def f_envconfig_TestNonBlankDefaultVar : Func :=
  { name := "envconfig.TestNonBlankDefaultVar"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call
                      "Setenv"
                      [(.lit (.str "ENV_CONFIG_DEFAULTVAR")), (.lit (.str "nondefaultval"))]))
                  (.seq
                    (.expr
                      (.call
                        "Setenv"
                        [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "requiredvalue"))]))
                    (.seq
                      (.seq
                        .skip
                        (.assign
                          "err"
                          (.call
                            "envconfig.Process"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                      (.seq
                        (.ifte
                          (.binop "!=" (.name "err") (.name "nil"))
                          (.expr (.call "Error" [(.call "Error" [])]))
                          .skip)
                        (.seq
                          .skip
                          (.ifte
                            (.binop
                              "!="
                              (.field (.name "s") "DefaultVar")
                              (.lit (.str "nondefaultval")))
                            (.expr
                              (.call
                                "Errorf"
                                [ (.lit (.str "expected %s, got %s"))
                                , (.lit (.str "nondefaultval"))
                                , (.field (.name "s") "DefaultVar") ]))
                            .skip))))))))) }

/-- `envconfig.TestExplicitBlankDefaultVar`  (from `envconfig_test.go`) -/
def f_envconfig_TestExplicitBlankDefaultVar : Func :=
  { name := "envconfig.TestExplicitBlankDefaultVar"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_DEFAULTVAR")), (.lit (.str ""))]))
                  (.seq
                    (.expr
                      (.call "Setenv" [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str ""))]))
                    (.seq
                      (.seq
                        .skip
                        (.assign
                          "err"
                          (.call
                            "envconfig.Process"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                      (.seq
                        (.ifte
                          (.binop "!=" (.name "err") (.name "nil"))
                          (.expr (.call "Error" [(.call "Error" [])]))
                          .skip)
                        (.seq
                          .skip
                          (.ifte
                            (.binop "!=" (.field (.name "s") "DefaultVar") (.lit (.str "")))
                            (.expr
                              (.call
                                "Errorf"
                                [ (.lit (.str "expected %s, got %s"))
                                , (.lit (.str "\\\"\\\""))
                                , (.field (.name "s") "DefaultVar") ]))
                            .skip))))))))) }

/-- `envconfig.TestAlternateNameDefaultVar`  (from `envconfig_test.go`) -/
def f_envconfig_TestAlternateNameDefaultVar : Func :=
  { name := "envconfig.TestAlternateNameDefaultVar"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr (.call "Setenv" [(.lit (.str "BROKER")), (.lit (.str "betterbroker"))]))
                  (.seq
                    (.expr
                      (.call "Setenv" [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                    (.seq
                      (.seq
                        .skip
                        (.assign
                          "err"
                          (.call
                            "envconfig.Process"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                      (.seq
                        (.ifte
                          (.binop "!=" (.name "err") (.name "nil"))
                          (.expr (.call "Error" [(.call "Error" [])]))
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.binop
                                "!="
                                (.field (.name "s") "NoPrefixDefault")
                                (.lit (.str "betterbroker")))
                              (.expr
                                (.call
                                  "Errorf"
                                  [ (.lit (.str "expected %q, got %q"))
                                  , (.lit (.str "betterbroker"))
                                  , (.field (.name "s") "NoPrefixDefault") ]))
                              .skip)
                            (.seq
                              (.expr (.call "Clearenv" []))
                              (.seq
                                (.expr
                                  (.call
                                    "Setenv"
                                    [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                                (.seq
                                  (.seq
                                    .skip
                                    (.assign
                                      "err"
                                      (.call
                                        "envconfig.Process"
                                        [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                                  (.seq
                                    (.ifte
                                      (.binop "!=" (.name "err") (.name "nil"))
                                      (.expr (.call "Error" [(.call "Error" [])]))
                                      .skip)
                                    (.seq
                                      .skip
                                      (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "NoPrefixDefault")
                                        (.lit (.str "127.0.0.1")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %q, got %q"))
                                        , (.lit (.str "127.0.0.1"))
                                        , (.field (.name "s") "NoPrefixDefault") ]))
                                        .skip))))))))))))))) }

/-- `envconfig.TestRequiredDefault`  (from `envconfig_test.go`) -/
def f_envconfig_TestRequiredDefault : Func :=
  { name := "envconfig.TestRequiredDefault"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call "Setenv" [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                  (.seq
                    (.seq
                      .skip
                      (.assign
                        "err"
                        (.call
                          "envconfig.Process"
                          [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                    (.seq
                      (.ifte
                        (.binop "!=" (.name "err") (.name "nil"))
                        (.expr (.call "Error" [(.call "Error" [])]))
                        .skip)
                      (.seq
                        .skip
                        (.ifte
                          (.binop
                            "!="
                            (.field (.name "s") "RequiredDefault")
                            (.lit (.str "foo2bar")))
                          (.expr
                            (.call
                              "Errorf"
                              [ (.lit (.str "expected %q, got %q"))
                              , (.lit (.str "foo2bar"))
                              , (.field (.name "s") "RequiredDefault") ]))
                          .skip)))))))) }

/-- `envconfig.TestPointerFieldBlank`  (from `envconfig_test.go`) -/
def f_envconfig_TestPointerFieldBlank : Func :=
  { name := "envconfig.TestPointerFieldBlank"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call "Setenv" [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                  (.seq
                    (.seq
                      .skip
                      (.assign
                        "err"
                        (.call
                          "envconfig.Process"
                          [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                    (.seq
                      (.ifte
                        (.binop "!=" (.name "err") (.name "nil"))
                        (.expr (.call "Error" [(.call "Error" [])]))
                        .skip)
                      (.seq
                        .skip
                        (.ifte
                          (.binop "!=" (.field (.name "s") "SomePointer") (.name "nil"))
                          (.expr
                            (.call
                              "Errorf"
                              [(.lit (.str "expected <nil>, got %q")), (.hole "op:indirection")]))
                          .skip)))))))) }

/-- `envconfig.TestEmptyMapFieldOverride`  (from `envconfig_test.go`) -/
def f_envconfig_TestEmptyMapFieldOverride : Func :=
  { name := "envconfig.TestEmptyMapFieldOverride"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call "Setenv" [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                  (.seq
                    (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_MAPFIELD")), (.lit (.str ""))]))
                    (.seq
                      (.seq
                        .skip
                        (.assign
                          "err"
                          (.call
                            "envconfig.Process"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                      (.seq
                        (.ifte
                          (.binop "!=" (.name "err") (.name "nil"))
                          (.expr (.call "Error" [(.call "Error" [])]))
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.binop "==" (.field (.name "s") "MapField") (.name "nil"))
                              (.expr
                                (.call "Error" [(.lit (.str "expected empty map, got <nil>"))]))
                              .skip)
                            (.seq
                              .skip
                              (.ifte
                                (.binop
                                  "!="
                                  (.mcall (.name "s") "MapField" [(.field (.name "s") "MapField")])
                                  (.lit (.int 0)))
                                (.expr
                                  (.call
                                    "Errorf"
                                    [ (.lit (.str "expected empty map, got map of size %d"))
                                    , (.mcall
                                        (.name "s")
                                        "MapField"
                                        [(.field (.name "s") "MapField")]) ]))
                                .skip))))))))))) }

/-- `envconfig.TestMustProcess`  (from `envconfig_test.go`) -/
def f_envconfig_TestMustProcess : Func :=
  { name := "envconfig.TestMustProcess"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_DEBUG")), (.lit (.str "true"))]))
                  (.seq
                    (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_PORT")), (.lit (.str "8080"))]))
                    (.seq
                      (.expr
                        (.call "Setenv" [(.lit (.str "ENV_CONFIG_RATE")), (.lit (.str "0.5"))]))
                      (.seq
                        (.expr
                          (.call "Setenv" [(.lit (.str "ENV_CONFIG_USER")), (.lit (.str "Kelsey"))]))
                        (.seq
                          (.expr
                            (.call
                              "Setenv"
                              [(.lit (.str "SERVICE_HOST")), (.lit (.str "127.0.0.1"))]))
                          (.seq
                            (.expr
                              (.call
                                "Setenv"
                                [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                            (.seq
                              (.expr
                                (.call
                                  "envconfig.MustProcess"
                                  [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                              (.seq
                                .skip
                                (.seq
                                  (.assign "m" (.call "make" [(.hole "lit:unquoted")]))
                                  (.expr
                                    (.call
                                      "envconfig.MustProcess"
                                      [(.lit (.str "env_config")), (.hole "op:addressOf")])))))))))))))) }

/-- `envconfig.TestEmbeddedStruct`  (from `envconfig_test.go`) -/
def f_envconfig_TestEmbeddedStruct : Func :=
  { name := "envconfig.TestEmbeddedStruct"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call
                      "Setenv"
                      [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "required"))]))
                  (.seq
                    (.expr
                      (.call "Setenv" [(.lit (.str "ENV_CONFIG_ENABLED")), (.lit (.str "true"))]))
                    (.seq
                      (.expr
                        (.call
                          "Setenv"
                          [(.lit (.str "ENV_CONFIG_EMBEDDEDPORT")), (.lit (.str "1234"))]))
                      (.seq
                        (.expr
                          (.call
                            "Setenv"
                            [(.lit (.str "ENV_CONFIG_MULTIWORDVAR")), (.lit (.str "foo"))]))
                        (.seq
                          (.expr
                            (.call
                              "Setenv"
                              [ (.lit (.str "ENV_CONFIG_MULTI_WORD_VAR_WITH_ALT"))
                              , (.lit (.str "bar")) ]))
                          (.seq
                            (.expr
                              (.call
                                "Setenv"
                                [ (.lit (.str "ENV_CONFIG_MULTI_WITH_DIFFERENT_ALT"))
                                , (.lit (.str "baz")) ]))
                            (.seq
                              (.expr
                                (.call
                                  "Setenv"
                                  [ (.lit (.str "ENV_CONFIG_EMBEDDED_WITH_ALT"))
                                  , (.lit (.str "foobar")) ]))
                              (.seq
                                (.expr
                                  (.call
                                    "Setenv"
                                    [(.lit (.str "ENV_CONFIG_SOMEPOINTER")), (.lit (.str "foobaz"))]))
                                (.seq
                                  (.expr
                                    (.call
                                      "Setenv"
                                      [ (.lit (.str "ENV_CONFIG_EMBEDDED_IGNORED"))
                                      , (.lit (.str "was-not-ignored")) ]))
                                  (.seq
                                    (.seq
                                      .skip
                                      (.assign
                                        "err"
                                        (.call
                                        "envconfig.Process"
                                        [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                                    (.seq
                                      (.ifte
                                        (.binop "!=" (.name "err") (.name "nil"))
                                        (.expr (.call "Error" [(.call "Error" [])]))
                                        .skip)
                                      (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.unop "!" (.field (.name "s") "Enabled"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %v, got %v"))
                                        , (.name "true")
                                        , (.field (.name "s") "Enabled") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "EmbeddedPort")
                                        (.lit (.int 1234)))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %d, got %v"))
                                        , (.lit (.int 1234))
                                        , (.field (.name "s") "EmbeddedPort") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "MultiWordVar")
                                        (.lit (.str "foo")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %s"))
                                        , (.lit (.str "foo"))
                                        , (.field (.name "s") "MultiWordVar") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.field (.name "s") "Embedded") "MultiWordVar")
                                        (.lit (.str "foo")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %s"))
                                        , (.lit (.str "foo"))
                                        , (.field (.field (.name "s") "Embedded") "MultiWordVar") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "MultiWordVarWithAlt")
                                        (.lit (.str "bar")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %s"))
                                        , (.lit (.str "bar"))
                                        , (.field (.name "s") "MultiWordVarWithAlt") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field
                                        (.field (.name "s") "Embedded")
                                        "MultiWordVarWithAlt")
                                        (.lit (.str "baz")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %s"))
                                        , (.lit (.str "baz"))
                                        , (.field
                                        (.field (.name "s") "Embedded")
                                        "MultiWordVarWithAlt") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "EmbeddedAlt")
                                        (.lit (.str "foobar")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %s"))
                                        , (.lit (.str "foobar"))
                                        , (.field (.name "s") "EmbeddedAlt") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.hole "op:indirection")
                                        (.lit (.str "foobaz")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %s"))
                                        , (.lit (.str "foobaz"))
                                        , (.hole "op:indirection") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "s") "EmbeddedIgnored")
                                        (.lit (.str "")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected empty string, got %#v"))
                                        , (.field (.name "s") "Ignored") ]))
                                        .skip)))))))))))))))))))))))))))))))) }

/-- `envconfig.TestEmbeddedButIgnoredStruct`  (from `envconfig_test.go`) -/
def f_envconfig_TestEmbeddedButIgnoredStruct : Func :=
  { name := "envconfig.TestEmbeddedButIgnoredStruct"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call
                      "Setenv"
                      [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "required"))]))
                  (.seq
                    (.expr
                      (.call
                        "Setenv"
                        [ (.lit (.str "ENV_CONFIG_FIRSTEMBEDDEDBUTIGNORED"))
                        , (.lit (.str "was-not-ignored")) ]))
                    (.seq
                      (.expr
                        (.call
                          "Setenv"
                          [ (.lit (.str "ENV_CONFIG_SECONDEMBEDDEDBUTIGNORED"))
                          , (.lit (.str "was-not-ignored")) ]))
                      (.seq
                        (.seq
                          .skip
                          (.assign
                            "err"
                            (.call
                              "envconfig.Process"
                              [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                        (.seq
                          (.ifte
                            (.binop "!=" (.name "err") (.name "nil"))
                            (.expr (.call "Error" [(.call "Error" [])]))
                            .skip)
                          (.seq
                            .skip
                            (.seq
                              (.ifte
                                (.binop
                                  "!="
                                  (.field (.name "s") "FirstEmbeddedButIgnored")
                                  (.lit (.str "")))
                                (.expr
                                  (.call
                                    "Errorf"
                                    [ (.lit (.str "expected empty string, got %#v"))
                                    , (.field (.name "s") "Ignored") ]))
                                .skip)
                              (.seq
                                .skip
                                (.ifte
                                  (.binop
                                    "!="
                                    (.field (.name "s") "SecondEmbeddedButIgnored")
                                    (.lit (.str "")))
                                  (.expr
                                    (.call
                                      "Errorf"
                                      [ (.lit (.str "expected empty string, got %#v"))
                                      , (.field (.name "s") "Ignored") ]))
                                  .skip)))))))))))) }

/-- `envconfig.TestNonPointerFailsProperly`  (from `envconfig_test.go`) -/
def f_envconfig_TestNonPointerFailsProperly : Func :=
  { name := "envconfig.TestNonPointerFailsProperly"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call "Setenv" [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "snap"))]))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "err"
                        (.call "envconfig.Process" [(.lit (.str "env_config")), (.name "s")]))
                      (.seq
                        .skip
                        (.ifte
                          (.binop
                            "!="
                            (.name "err")
                            (.field (.name "envconfig") "ErrInvalidSpecification"))
                          (.expr
                            (.call
                              "Errorf"
                              [ (.lit
                                  (.str "non-pointer should fail with ErrInvalidSpecification, was instead %s"))
                              , (.name "err") ]))
                          .skip)))))))) }

/-- `envconfig.TestCustomValueFields`  (from `envconfig_test.go`) -/
def f_envconfig_TestCustomValueFields : Func :=
  { name := "envconfig.TestCustomValueFields"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.setField (.name "s") "Baz" (.call "quoted" [(.call "new" [(.name "bracketed")])]))
                (.seq
                  (.expr (.call "Clearenv" []))
                  (.seq
                    (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_FOO")), (.lit (.str "foo"))]))
                    (.seq
                      (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_BAR")), (.lit (.str "bar"))]))
                      (.seq
                        (.expr
                          (.call "Setenv" [(.lit (.str "ENV_CONFIG_BAZ")), (.lit (.str "baz"))]))
                        (.seq
                          (.expr
                            (.call
                              "Setenv"
                              [(.lit (.str "ENV_CONFIG_STRUCT")), (.lit (.str "inner"))]))
                          (.seq
                            (.seq
                              .skip
                              (.assign
                                "err"
                                (.call
                                  "envconfig.Process"
                                  [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                            (.seq
                              (.ifte
                                (.binop "!=" (.name "err") (.name "nil"))
                                (.expr (.call "Error" [(.call "Error" [])]))
                                .skip)
                              (.seq
                                (.seq .skip (.assign "want" (.lit (.str "foo"))))
                                (.seq
                                  (.ifte
                                    (.binop "!=" (.field (.name "s") "Foo") (.name "want"))
                                    (.expr
                                      (.call
                                        "Errorf"
                                        [ (.lit (.str "foo: got %#q, want %#q"))
                                        , (.field (.name "s") "Foo")
                                        , (.name "want") ]))
                                    .skip)
                                  (.seq
                                    (.seq .skip (.assign "want" (.lit (.str "[bar]"))))
                                    (.seq
                                      (.ifte
                                        (.binop "!=" (.mcall (.name "s") "Bar" []) (.name "want"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "bar: got %#q, want %#q"))
                                        , (.field (.name "s") "Bar")
                                        , (.name "want") ]))
                                        .skip)
                                      (.seq
                                        (.seq .skip (.assign "want" (.hole "lit:unquoted")))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.mcall (.name "s") "Baz" []) (.name "want"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.hole "lit:unquoted")
                                        , (.field (.name "s") "Baz")
                                        , (.name "want") ]))
                                        .skip)
                                        (.seq
                                        (.seq .skip (.assign "want" (.hole "lit:unquoted")))
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.field (.name "s") "Struct") "Inner")
                                        (.name "want"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.hole "lit:unquoted")
                                        , (.field (.field (.name "s") "Struct") "Inner")
                                        , (.name "want") ]))
                                        .skip)))))))))))))))))) }

/-- `envconfig.TestCustomPointerFields`  (from `envconfig_test.go`) -/
def f_envconfig_TestCustomPointerFields : Func :=
  { name := "envconfig.TestCustomPointerFields"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.setField (.name "s") "Bar" (.call "new" [(.name "bracketed")]))
                (.seq
                  (.setField (.name "s") "Baz" (.hole "op:addressOf"))
                  (.seq
                    (.expr (.call "Clearenv" []))
                    (.seq
                      (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_FOO")), (.lit (.str "foo"))]))
                      (.seq
                        (.expr
                          (.call "Setenv" [(.lit (.str "ENV_CONFIG_BAR")), (.lit (.str "bar"))]))
                        (.seq
                          (.expr
                            (.call "Setenv" [(.lit (.str "ENV_CONFIG_BAZ")), (.lit (.str "baz"))]))
                          (.seq
                            (.expr
                              (.call
                                "Setenv"
                                [(.lit (.str "ENV_CONFIG_STRUCT")), (.lit (.str "inner"))]))
                            (.seq
                              (.seq
                                .skip
                                (.assign
                                  "err"
                                  (.call
                                    "envconfig.Process"
                                    [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                              (.seq
                                (.ifte
                                  (.binop "!=" (.name "err") (.name "nil"))
                                  (.expr (.call "Error" [(.call "Error" [])]))
                                  .skip)
                                (.seq
                                  (.seq .skip (.assign "want" (.lit (.str "foo"))))
                                  (.seq
                                    (.ifte
                                      (.binop "!=" (.field (.name "s") "Foo") (.name "want"))
                                      (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "foo: got %#q, want %#q"))
                                        , (.field (.name "s") "Foo")
                                        , (.name "want") ]))
                                      .skip)
                                    (.seq
                                      (.seq .skip (.assign "want" (.lit (.str "[bar]"))))
                                      (.seq
                                        (.ifte
                                        (.binop "!=" (.mcall (.name "s") "Bar" []) (.name "want"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "bar: got %#q, want %#q"))
                                        , (.field (.name "s") "Bar")
                                        , (.name "want") ]))
                                        .skip)
                                        (.seq
                                        (.seq .skip (.assign "want" (.hole "lit:unquoted")))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.mcall (.name "s") "Baz" []) (.name "want"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.hole "lit:unquoted")
                                        , (.field (.name "s") "Baz")
                                        , (.name "want") ]))
                                        .skip)
                                        (.seq
                                        (.seq .skip (.assign "want" (.hole "lit:unquoted")))
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.field (.name "s") "Struct") "Inner")
                                        (.name "want"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.hole "lit:unquoted")
                                        , (.field (.field (.name "s") "Struct") "Inner")
                                        , (.name "want") ]))
                                        .skip))))))))))))))))))) }

/-- `envconfig.TestEmptyPrefixUsesFieldNames`  (from `envconfig_test.go`) -/
def f_envconfig_TestEmptyPrefixUsesFieldNames : Func :=
  { name := "envconfig.TestEmptyPrefixUsesFieldNames"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr (.call "Setenv" [(.lit (.str "REQUIREDVAR")), (.lit (.str "foo"))]))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "err"
                        (.call "envconfig.Process" [(.lit (.str "")), (.hole "op:addressOf")]))
                      (.seq
                        .skip
                        (.seq
                          (.ifte
                            (.binop "!=" (.name "err") (.name "nil"))
                            (.expr
                              (.call "Errorf" [(.lit (.str "Process failed: %s")), (.name "err")]))
                            .skip)
                          (.seq
                            .skip
                            (.ifte
                              (.binop "!=" (.field (.name "s") "RequiredVar") (.lit (.str "foo")))
                              (.expr
                                (.call
                                  "Errorf"
                                  [(.hole "lit:unquoted"), (.field (.name "s") "RequiredVar")]))
                              .skip)))))))))) }

/-- `envconfig.TestNestedStructVarName`  (from `envconfig_test.go`) -/
def f_envconfig_TestNestedStructVarName : Func :=
  { name := "envconfig.TestNestedStructVarName"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call
                      "Setenv"
                      [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "required"))]))
                  (.seq
                    .skip
                    (.seq
                      (.assign "val" (.lit (.str "found with only short name")))
                      (.seq
                        (.expr (.call "Setenv" [(.lit (.str "INNER")), (.name "val")]))
                        (.seq
                          (.seq
                            .skip
                            (.assign
                              "err"
                              (.call
                                "envconfig.Process"
                                [(.lit (.str "env_config")), (.hole "op:addressOf")])))
                          (.seq
                            (.ifte
                              (.binop "!=" (.name "err") (.name "nil"))
                              (.expr (.call "Error" [(.call "Error" [])]))
                              .skip)
                            (.seq
                              .skip
                              (.ifte
                                (.binop
                                  "!="
                                  (.field (.field (.name "s") "NestedSpecification") "Property")
                                  (.name "val"))
                                (.expr
                                  (.call
                                    "Errorf"
                                    [ (.lit (.str "expected %s, got %s"))
                                    , (.name "val")
                                    , (.field (.field (.name "s") "NestedSpecification") "Property") ]))
                                .skip))))))))))) }

/-- `envconfig.TestTextUnmarshalerError`  (from `envconfig_test.go`) -/
def f_envconfig_TestTextUnmarshalerError : Func :=
  { name := "envconfig.TestTextUnmarshalerError"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call "Setenv" [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                  (.seq
                    (.expr
                      (.call
                        "Setenv"
                        [(.lit (.str "ENV_CONFIG_DATETIME")), (.lit (.str "I'M NOT A DATE"))]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "err"
                          (.call
                            "envconfig.Process"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                        (.seq
                          .skip
                          (.seq
                            (.assign "v" (.name "err"))
                            (.seq
                              .skip
                              (.seq
                                (.ifte
                                  (.unop "!" (.name "ok"))
                                  (.expr
                                    (.call
                                      "Errorf"
                                      [(.lit (.str "expected ParseError, got %v")), (.name "v")]))
                                  .skip)
                                (.seq
                                  .skip
                                  (.seq
                                    (.ifte
                                      (.binop
                                        "!="
                                        (.field (.name "v") "FieldName")
                                        (.lit (.str "Datetime")))
                                      (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %v"))
                                        , (.lit (.str "Datetime"))
                                        , (.field (.name "v") "FieldName") ]))
                                      .skip)
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "expectedLowLevelError"
                                        (.mcall
                                        (.name "time")
                                        "RFC3339"
                                        [ (.field (.name "time") "RFC3339")
                                        , (.lit (.str "I'M NOT A DATE"))
                                        , (.lit (.str "2006"))
                                        , (.lit (.str "I'M NOT A DATE")) ]))
                                        (.seq
                                        .skip
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.mcall (.name "v") "Err" [])
                                        (.call "Error" []))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %s"))
                                        , (.name "expectedLowLevelError")
                                        , (.field (.name "v") "Err") ]))
                                        .skip))))))))))))))))) }

/-- `envconfig.TestBinaryUnmarshalerError`  (from `envconfig_test.go`) -/
def f_envconfig_TestBinaryUnmarshalerError : Func :=
  { name := "envconfig.TestBinaryUnmarshalerError"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr
                    (.call "Setenv" [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                  (.seq
                    (.expr
                      (.call
                        "Setenv"
                        [(.lit (.str "ENV_CONFIG_URLPOINTER")), (.lit (.str "http://%41:8080/"))]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "err"
                          (.call
                            "envconfig.Process"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                        (.seq
                          .skip
                          (.seq
                            (.assign "v" (.name "err"))
                            (.seq
                              .skip
                              (.seq
                                (.ifte
                                  (.unop "!" (.name "ok"))
                                  (.expr
                                    (.call
                                      "Fatalf"
                                      [ (.lit (.str "expected ParseError, got %T %v"))
                                      , (.name "err")
                                      , (.name "err") ]))
                                  .skip)
                                (.seq
                                  .skip
                                  (.seq
                                    (.ifte
                                      (.binop
                                        "!="
                                        (.field (.name "v") "FieldName")
                                        (.lit (.str "UrlPointer")))
                                      (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit (.str "expected %s, got %v"))
                                        , (.lit (.str "UrlPointer"))
                                        , (.field (.name "v") "FieldName") ]))
                                      .skip)
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign "ue" (.field (.name "v") "Err"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.unop "!" (.name "ok"))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit
                                        (.str "expected error type to be \\\"*url.Error\\\", got %T"))
                                        , (.field (.name "v") "Err") ]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "ue") "Op")
                                        (.lit (.str "parse")))
                                        (.expr
                                        (.call
                                        "Errorf"
                                        [ (.lit
                                        (.str "expected error op to be \\\"parse\\\", got %q"))
                                        , (.field (.name "ue") "Op") ]))
                                        .skip))))))))))))))))))) }

/-- `envconfig.TestCheckDisallowedOnlyAllowed`  (from `envconfig_test.go`) -/
def f_envconfig_TestCheckDisallowedOnlyAllowed : Func :=
  { name := "envconfig.TestCheckDisallowedOnlyAllowed"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_DEBUG")), (.lit (.str "true"))]))
                  (.seq
                    (.expr
                      (.call "Setenv" [(.lit (.str "UNRELATED_ENV_VAR")), (.lit (.str "true"))]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "err"
                          (.call
                            "envconfig.CheckDisallowed"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                        (.seq
                          .skip
                          (.ifte
                            (.binop "!=" (.name "err") (.name "nil"))
                            (.expr
                              (.call
                                "Errorf"
                                [(.lit (.str "expected no error, got %s")), (.name "err")]))
                            .skip))))))))) }

/-- `envconfig.TestCheckDisallowedMispelled`  (from `envconfig_test.go`) -/
def f_envconfig_TestCheckDisallowedMispelled : Func :=
  { name := "envconfig.TestCheckDisallowedMispelled"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_DEBUG")), (.lit (.str "true"))]))
                  (.seq
                    (.expr
                      (.call "Setenv" [(.lit (.str "ENV_CONFIG_ZEBUG")), (.lit (.str "false"))]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "err"
                          (.call
                            "envconfig.CheckDisallowed"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                        (.seq
                          (.seq
                            .skip
                            (.assign
                              "experr"
                              (.lit (.str "unknown environment variable ENV_CONFIG_ZEBUG"))))
                          (.ifte
                            (.binop "!=" (.call "Error" []) (.name "experr"))
                            (.expr
                              (.call
                                "Errorf"
                                [ (.lit (.str "expected %s, got %s"))
                                , (.name "experr")
                                , (.name "err") ]))
                            .skip))))))))) }

/-- `envconfig.TestCheckDisallowedIgnored`  (from `envconfig_test.go`) -/
def f_envconfig_TestCheckDisallowedIgnored : Func :=
  { name := "envconfig.TestCheckDisallowedIgnored"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_DEBUG")), (.lit (.str "true"))]))
                  (.seq
                    (.expr
                      (.call "Setenv" [(.lit (.str "ENV_CONFIG_IGNORED")), (.lit (.str "false"))]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "err"
                          (.call
                            "envconfig.CheckDisallowed"
                            [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                        (.seq
                          (.seq
                            .skip
                            (.assign
                              "experr"
                              (.lit (.str "unknown environment variable ENV_CONFIG_IGNORED"))))
                          (.ifte
                            (.binop "!=" (.call "Error" []) (.name "experr"))
                            (.expr
                              (.call
                                "Errorf"
                                [ (.lit (.str "expected %s, got %s"))
                                , (.name "experr")
                                , (.name "err") ]))
                            .skip))))))))) }

/-- `envconfig.TestErrorMessageForRequiredAltVar`  (from `envconfig_test.go`) -/
def f_envconfig_TestErrorMessageForRequiredAltVar : Func :=
  { name := "envconfig.TestErrorMessageForRequiredAltVar"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "err"
                      (.call
                        "envconfig.Process"
                        [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                    (.seq
                      .skip
                      (.seq
                        (.ifte
                          (.binop "==" (.name "err") (.name "nil"))
                          (.expr
                            (.call
                              "Error"
                              [(.lit (.str "no failure when missing required variable"))]))
                          .skip)
                        (.seq
                          .skip
                          (.ifte
                            (.unop
                              "!"
                              (.call "Contains" [(.call "Error" []), (.lit (.str " BAR "))]))
                            (.expr
                              (.call
                                "Errorf"
                                [ (.lit
                                    (.str "expected error message to contain BAR, got \\\"%v\\\""))
                                , (.name "err") ]))
                            .skip))))))))) }

/-- `envconfig.bracketed.Set`  (from `envconfig_test.go`) -/
def f_envconfig_bracketed_Set : Func :=
  { name := "envconfig.bracketed.Set"
  , params := ["b", "value"]
  , body := (.seq (.hole "assign:lhs:indirection") (.ret (.name "nil"))) }

/-- `envconfig.bracketed.String`  (from `envconfig_test.go`) -/
def f_envconfig_bracketed_String : Func :=
  { name := "envconfig.bracketed.String"
  , params := ["b"]
  , body := (.ret (.call "string" [(.name "b")])) }

/-- `envconfig.quoted.Decode`  (from `envconfig_test.go`) -/
def f_envconfig_quoted_Decode : Func :=
  { name := "envconfig.quoted.Decode"
  , params := ["d", "value"]
  , body := (.ret
            (.call
              "Set"
              [ (.binop
                  "+"
                  (.binop "+" (.hole "lit:unquoted") (.name "value"))
                  (.hole "lit:unquoted")) ])) }

/-- `envconfig.setterStruct.Set`  (from `envconfig_test.go`) -/
def f_envconfig_setterStruct_Set : Func :=
  { name := "envconfig.setterStruct.Set"
  , params := ["ss", "value"]
  , body := (.seq
            (.setField
              (.name "ss")
              "Inner"
              (.call "Sprintf" [(.lit (.str "setterstruct{%q}")), (.name "value")]))
            (.ret (.name "nil"))) }

/-- `envconfig.BenchmarkGatherInfo`  (from `envconfig_test.go`) -/
def f_envconfig_BenchmarkGatherInfo : Func :=
  { name := "envconfig.BenchmarkGatherInfo"
  , params := ["b"]
  , body := (.seq
            (.expr (.call "Clearenv" []))
            (.seq
              (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_DEBUG")), (.lit (.str "true"))]))
              (.seq
                (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_PORT")), (.lit (.str "8080"))]))
                (.seq
                  (.expr (.call "Setenv" [(.lit (.str "ENV_CONFIG_RATE")), (.lit (.str "0.5"))]))
                  (.seq
                    (.expr
                      (.call "Setenv" [(.lit (.str "ENV_CONFIG_USER")), (.lit (.str "Kelsey"))]))
                    (.seq
                      (.expr
                        (.call "Setenv" [(.lit (.str "ENV_CONFIG_TIMEOUT")), (.lit (.str "2m"))]))
                      (.seq
                        (.expr
                          (.call
                            "Setenv"
                            [(.lit (.str "ENV_CONFIG_ADMINUSERS")), (.lit (.str "John,Adam,Will"))]))
                        (.seq
                          (.expr
                            (.call
                              "Setenv"
                              [(.lit (.str "ENV_CONFIG_MAGICNUMBERS")), (.lit (.str "5,10,20"))]))
                          (.seq
                            (.expr
                              (.call
                                "Setenv"
                                [ (.lit (.str "ENV_CONFIG_COLORCODES"))
                                , (.lit (.str "red:1,green:2,blue:3")) ]))
                            (.seq
                              (.expr
                                (.call
                                  "Setenv"
                                  [(.lit (.str "SERVICE_HOST")), (.lit (.str "127.0.0.1"))]))
                              (.seq
                                (.expr
                                  (.call
                                    "Setenv"
                                    [(.lit (.str "ENV_CONFIG_TTL")), (.lit (.str "30"))]))
                                (.seq
                                  (.expr
                                    (.call
                                      "Setenv"
                                      [(.lit (.str "ENV_CONFIG_REQUIREDVAR")), (.lit (.str "foo"))]))
                                  (.seq
                                    (.expr
                                      (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_IGNORED"))
                                        , (.lit (.str "was-not-ignored")) ]))
                                    (.seq
                                      (.expr
                                        (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_OUTER_INNER"))
                                        , (.lit (.str "iamnested")) ]))
                                      (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_AFTERNESTED"))
                                        , (.lit (.str "after")) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [(.lit (.str "ENV_CONFIG_HONOR")), (.lit (.str "honor"))]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_DATETIME"))
                                        , (.lit (.str "2016-08-16T18:57:05Z")) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Setenv"
                                        [ (.lit (.str "ENV_CONFIG_MULTI_WORD_VAR_WITH_AUTO_SPLIT"))
                                        , (.lit (.str "24")) ]))
                                        (.hole "control:FOR"))))))))))))))))))) }

/-- `envconfig_test.go:envconfig.envconfig_test.go`  (from `envconfig_test.go`) -/
def f_envconfig_test_go_envconfig_envconfig_test_go : Func :=
  { name := "envconfig_test.go:envconfig.envconfig_test.go"
  , params := []
  , body := (.seq
            (.hole "stmt:IMPORT")
            (.seq
              (.hole "stmt:IMPORT")
              (.seq
                (.hole "stmt:IMPORT")
                (.seq
                  (.hole "stmt:IMPORT")
                  (.seq
                    (.hole "stmt:IMPORT")
                    (.seq
                      (.hole "stmt:IMPORT")
                      (.seq
                        (.hole "stmt:IMPORT")
                        (.seq
                          (.hole "stmt:TYPE_DECL")
                          (.seq
                            (.hole "stmt:TYPE_DECL")
                            (.seq
                              (.hole "stmt:TYPE_DECL")
                              (.seq
                                (.hole "stmt:TYPE_DECL")
                                (.seq
                                  (.hole "stmt:TYPE_DECL")
                                  (.seq
                                    (.hole "stmt:TYPE_DECL")
                                    (.seq (.hole "stmt:TYPE_DECL") (.hole "stmt:TYPE_DECL"))))))))))))))) }

/-- `envconfig.implementsInterface`  (from `usage.go`) -/
def f_envconfig_implementsInterface : Func :=
  { name := "envconfig.implementsInterface"
  , params := ["t"]
  , body := (.ret
            (.binop
              "||"
              (.binop
                "||"
                (.binop
                  "||"
                  (.binop
                    "||"
                    (.binop
                      "||"
                      (.binop
                        "||"
                        (.binop
                          "||"
                          (.call "Implements" [(.field (.name "envconfig") "decoderType")])
                          (.call "Implements" [(.field (.name "envconfig") "decoderType")]))
                        (.call "Implements" [(.field (.name "envconfig") "setterType")]))
                      (.call "Implements" [(.field (.name "envconfig") "setterType")]))
                    (.call "Implements" [(.field (.name "envconfig") "textUnmarshalerType")]))
                  (.call "Implements" [(.field (.name "envconfig") "textUnmarshalerType")]))
                (.call "Implements" [(.field (.name "envconfig") "binaryUnmarshalerType")]))
              (.call "Implements" [(.field (.name "envconfig") "binaryUnmarshalerType")]))) }

/-- `envconfig.toTypeDescription`  (from `usage.go`) -/
def f_envconfig_toTypeDescription : Func :=
  { name := "envconfig.toTypeDescription"
  , params := ["t"]
  , body := (.seq
            (.hole "control:SWITCH")
            (.ret (.call "Sprintf" [(.lit (.str "%+v")), (.name "t")]))) }

/-- `envconfig.Usage`  (from `usage.go`) -/
def f_envconfig_Usage : Func :=
  { name := "envconfig.Usage"
  , params := ["prefix", "spec"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "tabs"
                (.mcall
                  (.name "os")
                  "Stdout"
                  [ (.field (.name "os") "Stdout")
                  , (.lit (.int 1))
                  , (.lit (.int 0))
                  , (.lit (.int 4))
                  , (.lit (.str " "))
                  , (.lit (.int 0)) ]))
              (.seq
                .skip
                (.seq
                  (.assign
                    "err"
                    (.call
                      "envconfig.Usagef"
                      [ (.name "prefix")
                      , (.name "spec")
                      , (.name "tabs")
                      , (.field (.name "envconfig") "DefaultTableFormat") ]))
                  (.seq (.expr (.call "Flush" [])) (.ret (.name "err"))))))) }

/-- `envconfig.Usagef.<lambda>0`  (from `usage.go`) -/
def f_envconfig_Usagef__lambda_0 : Func :=
  { name := "envconfig.Usagef.<lambda>0"
  , params := ["v"]
  , body := (.ret (.field (.name "v") "Key")) }

/-- `envconfig.Usagef.<lambda>1`  (from `usage.go`) -/
def f_envconfig_Usagef__lambda_1 : Func :=
  { name := "envconfig.Usagef.<lambda>1"
  , params := ["v"]
  , body := (.ret (.mcall (.name "v") "Tags" [(.lit (.str "desc"))])) }

/-- `envconfig.Usagef.<lambda>2`  (from `usage.go`) -/
def f_envconfig_Usagef__lambda_2 : Func :=
  { name := "envconfig.Usagef.<lambda>2"
  , params := ["v"]
  , body := (.ret (.call "envconfig.toTypeDescription" [(.mcall (.name "v") "Field" [])])) }

/-- `envconfig.Usagef.<lambda>3`  (from `usage.go`) -/
def f_envconfig_Usagef__lambda_3 : Func :=
  { name := "envconfig.Usagef.<lambda>3"
  , params := ["v"]
  , body := (.ret (.mcall (.name "v") "Tags" [(.lit (.str "default"))])) }

/-- `envconfig.Usagef.<lambda>4`  (from `usage.go`) -/
def f_envconfig_Usagef__lambda_4 : Func :=
  { name := "envconfig.Usagef.<lambda>4"
  , params := ["v"]
  , body := (.seq
            .skip
            (.seq
              (.assign "req" (.mcall (.name "v") "Tags" [(.lit (.str "required"))]))
              (.seq
                .skip
                (.seq
                  (.ifte
                    (.binop "!=" (.name "req") (.lit (.str "")))
                    (.seq
                      .skip
                      (.seq
                        (.assign "reqB" (.call "ParseBool" [(.name "req")]))
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.binop "!=" (.name "err") (.name "nil"))
                              (.ret (.lit (.str "")))
                              .skip)
                            (.seq
                              .skip
                              (.ifte (.name "reqB") (.assign "req" (.lit (.str "true"))) .skip))))))
                    .skip)
                  (.ret (.name "req")))))) }

/-- `envconfig.Usagef`  (from `usage.go`) -/
def f_envconfig_Usagef : Func :=
  { name := "envconfig.Usagef"
  , params := ["prefix", "spec", "out", "format"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "functions"
                (.call
                  "FuncMap"
                  [ (.fnref "envconfig.Usagef.<lambda>0")
                  , (.fnref "envconfig.Usagef.<lambda>1")
                  , (.fnref "envconfig.Usagef.<lambda>2")
                  , (.fnref "envconfig.Usagef.<lambda>3")
                  , (.fnref "envconfig.Usagef.<lambda>4") ]))
              (.seq
                .skip
                (.seq
                  (.assign "tmpl" (.call "Parse" [(.name "format")]))
                  (.seq
                    .skip
                    (.seq
                      (.ifte (.binop "!=" (.name "err") (.name "nil")) (.ret (.name "err")) .skip)
                      (.ret
                        (.call
                          "envconfig.Usaget"
                          [(.name "prefix"), (.name "spec"), (.name "out"), (.name "tmpl")])))))))) }

/-- `envconfig.Usaget`  (from `usage.go`) -/
def f_envconfig_Usaget : Func :=
  { name := "envconfig.Usaget"
  , params := ["prefix", "spec", "out", "tmpl"]
  , body := (.seq
            .skip
            (.seq
              (.assign "infos" (.call "envconfig.gatherInfo" [(.name "prefix"), (.name "spec")]))
              (.seq
                .skip
                (.seq
                  (.ifte (.binop "!=" (.name "err") (.name "nil")) (.ret (.name "err")) .skip)
                  (.ret (.call "Execute" [(.name "out"), (.name "infos")])))))) }

/-- `usage.go:envconfig.usage.go`  (from `usage.go`) -/
def f_usage_go_envconfig_usage_go : Func :=
  { name := "usage.go:envconfig.usage.go"
  , params := []
  , body := (.seq
            (.hole "stmt:IMPORT")
            (.seq
              (.hole "stmt:IMPORT")
              (.seq
                (.hole "stmt:IMPORT")
                (.seq
                  (.hole "stmt:IMPORT")
                  (.seq
                    (.hole "stmt:IMPORT")
                    (.seq
                      (.hole "stmt:IMPORT")
                      (.seq
                        (.hole "stmt:IMPORT")
                        (.seq (.hole "stmt:IMPORT") (.hole "stmt:IMPORT"))))))))) }

/-- `envconfig.TestMain`  (from `usage_test.go`) -/
def f_envconfig_TestMain : Func :=
  { name := "envconfig.TestMain"
  , params := ["m"]
  , body := (.seq
            .skip
            (.seq
              (.assign "data" (.call "ReadFile" [(.lit (.str "testdata/default_table.txt"))]))
              (.seq
                .skip
                (.seq
                  (.ifte
                    (.binop "!=" (.name "err") (.name "nil"))
                    (.expr (.call "Fatal" [(.name "err")]))
                    .skip)
                  (.seq
                    (.setField
                      (.name "envconfig")
                      "testUsageTableResult"
                      (.call "string" [(.name "data")]))
                    (.seq
                      (.hole "assign:arity")
                      (.seq
                        .skip
                        (.seq
                          (.ifte
                            (.binop "!=" (.name "err") (.name "nil"))
                            (.expr (.call "Fatal" [(.name "err")]))
                            .skip)
                          (.seq
                            (.setField
                              (.name "envconfig")
                              "testUsageListResult"
                              (.call "string" [(.name "data")]))
                            (.seq
                              (.hole "assign:arity")
                              (.seq
                                .skip
                                (.seq
                                  (.ifte
                                    (.binop "!=" (.name "err") (.name "nil"))
                                    (.expr (.call "Fatal" [(.name "err")]))
                                    .skip)
                                  (.seq
                                    (.setField
                                      (.name "envconfig")
                                      "testUsageCustomResult"
                                      (.call "string" [(.name "data")]))
                                    (.seq
                                      (.hole "assign:arity")
                                      (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "err") (.name "nil"))
                                        (.expr (.call "Fatal" [(.name "err")]))
                                        .skip)
                                        (.seq
                                        (.setField
                                        (.name "envconfig")
                                        "testUsageBadFormatResult"
                                        (.call "string" [(.name "data")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "retCode" (.call "Run" []))
                                        (.expr (.call "Exit" [(.name "retCode")]))))))))))))))))))))) }

/-- `envconfig.compareUsage`  (from `usage_test.go`) -/
def f_envconfig_compareUsage : Func :=
  { name := "envconfig.compareUsage"
  , params := ["want", "got", "t"]
  , body := (.seq
            (.assign
              "got"
              (.call "ReplaceAll" [(.name "got"), (.lit (.str " ")), (.lit (.str "."))]))
            (.seq
              .skip
              (.ifte
                (.binop "!=" (.name "want") (.name "got"))
                (.seq
                  .skip
                  (.seq
                    (.assign "shortest" (.call "len" [(.name "want")]))
                    (.seq
                      .skip
                      (.seq
                        (.ifte
                          (.binop "<" (.call "len" [(.name "got")]) (.name "shortest"))
                          (.assign "shortest" (.call "len" [(.name "got")]))
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.binop
                                "!="
                                (.call "len" [(.name "want")])
                                (.call "len" [(.name "got")]))
                              (.expr
                                (.call
                                  "Errorf"
                                  [ (.lit (.str "expected result length of %d, found %d"))
                                  , (.call "len" [(.name "want")])
                                  , (.call "len" [(.name "got")]) ]))
                              .skip)
                            (.seq
                              (.hole "control:FOR")
                              (.expr
                                (.call
                                  "Errorf"
                                  [ (.lit
                                      (.str "Complete Expected:\\n'%s'\\nComplete Found:\\n'%s'\\n"))
                                  , (.name "want")
                                  , (.name "got") ])))))))))
                .skip))) }

/-- `envconfig.TestUsageDefault`  (from `usage_test.go`) -/
def f_envconfig_TestUsageDefault : Func :=
  { name := "envconfig.TestUsageDefault"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  .skip
                  (.seq
                    (.assign "save" (.field (.name "os") "Stdout"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "r" (.call "Pipe" []))
                        (.seq
                          (.setField (.name "os") "Stdout" (.name "w"))
                          (.seq
                            .skip
                            (.seq
                              (.assign
                                "err"
                                (.call
                                  "envconfig.Usage"
                                  [(.lit (.str "env_config")), (.hole "op:addressOf")]))
                              (.seq
                                .skip
                                (.seq
                                  (.assign "outC" (.call "make" [(.hole "lit:unquoted")]))
                                  (.seq
                                    (.expr (.call "Close" []))
                                    (.seq
                                      (.setField (.name "os") "Stdout" (.name "save"))
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign "out" (.hole "op:unknown"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "err") (.name "nil"))
                                        (.expr (.call "Error" [(.call "Error" [])]))
                                        .skip)
                                        (.expr
                                        (.mcall
                                        (.name "envconfig")
                                        "testUsageTableResult"
                                        [ (.field (.name "envconfig") "testUsageTableResult")
                                        , (.name "out")
                                        , (.name "t") ])))))))))))))))))))) }

/-- `envconfig.TestUsageTable`  (from `usage_test.go`) -/
def f_envconfig_TestUsageTable : Func :=
  { name := "envconfig.TestUsageTable"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "buf"
                      (.mcall (.name "bytes") "Buffer" [(.field (.name "bytes") "Buffer")]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "tabs"
                          (.call
                            "NewWriter"
                            [ (.name "buf")
                            , (.lit (.int 1))
                            , (.lit (.int 0))
                            , (.lit (.int 4))
                            , (.lit (.str " "))
                            , (.lit (.int 0)) ]))
                        (.seq
                          .skip
                          (.seq
                            (.assign
                              "err"
                              (.call
                                "envconfig.Usagef"
                                [ (.lit (.str "env_config"))
                                , (.hole "op:addressOf")
                                , (.name "tabs")
                                , (.field (.name "envconfig") "DefaultTableFormat") ]))
                            (.seq
                              (.expr (.call "Flush" []))
                              (.seq
                                .skip
                                (.seq
                                  (.ifte
                                    (.binop "!=" (.name "err") (.name "nil"))
                                    (.expr (.call "Error" [(.call "Error" [])]))
                                    .skip)
                                  (.expr
                                    (.mcall
                                      (.name "envconfig")
                                      "testUsageTableResult"
                                      [ (.field (.name "envconfig") "testUsageTableResult")
                                      , (.call "String" [])
                                      , (.name "t") ])))))))))))))) }

/-- `envconfig.TestUsageList`  (from `usage_test.go`) -/
def f_envconfig_TestUsageList : Func :=
  { name := "envconfig.TestUsageList"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "buf"
                      (.mcall (.name "bytes") "Buffer" [(.field (.name "bytes") "Buffer")]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "err"
                          (.call
                            "envconfig.Usagef"
                            [ (.lit (.str "env_config"))
                            , (.hole "op:addressOf")
                            , (.name "buf")
                            , (.field (.name "envconfig") "DefaultListFormat") ]))
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.binop "!=" (.name "err") (.name "nil"))
                              (.expr (.call "Error" [(.call "Error" [])]))
                              .skip)
                            (.expr
                              (.mcall
                                (.name "envconfig")
                                "testUsageListResult"
                                [ (.field (.name "envconfig") "testUsageListResult")
                                , (.call "String" [])
                                , (.name "t") ]))))))))))) }

/-- `envconfig.TestUsageCustomFormat`  (from `usage_test.go`) -/
def f_envconfig_TestUsageCustomFormat : Func :=
  { name := "envconfig.TestUsageCustomFormat"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "buf"
                      (.mcall (.name "bytes") "Buffer" [(.field (.name "bytes") "Buffer")]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "err"
                          (.call
                            "envconfig.Usagef"
                            [ (.lit (.str "env_config"))
                            , (.hole "op:addressOf")
                            , (.name "buf")
                            , (.lit
                                (.str "{{range .}}{{usage_key .}}={{usage_description .}}\\n{{end}}")) ]))
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.binop "!=" (.name "err") (.name "nil"))
                              (.expr (.call "Error" [(.call "Error" [])]))
                              .skip)
                            (.expr
                              (.mcall
                                (.name "envconfig")
                                "testUsageCustomResult"
                                [ (.field (.name "envconfig") "testUsageCustomResult")
                                , (.call "String" [])
                                , (.name "t") ]))))))))))) }

/-- `envconfig.TestUsageUnknownKeyFormat`  (from `usage_test.go`) -/
def f_envconfig_TestUsageUnknownKeyFormat : Func :=
  { name := "envconfig.TestUsageUnknownKeyFormat"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                .skip
                (.seq
                  (.assign
                    "unknownError"
                    (.lit
                      (.str "template: envconfig:1:2: executing \\\"envconfig\\\" at <.UnknownKey>")))
                  (.seq
                    (.expr (.call "Clearenv" []))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "buf"
                          (.mcall (.name "bytes") "Buffer" [(.field (.name "bytes") "Buffer")]))
                        (.seq
                          .skip
                          (.seq
                            (.assign
                              "err"
                              (.call
                                "envconfig.Usagef"
                                [ (.lit (.str "env_config"))
                                , (.hole "op:addressOf")
                                , (.name "buf")
                                , (.lit (.str "{{.UnknownKey}}")) ]))
                            (.seq
                              .skip
                              (.seq
                                (.ifte
                                  (.binop "==" (.name "err") (.name "nil"))
                                  (.expr
                                    (.call
                                      "Errorf"
                                      [ (.lit
                                        (.str "expected 'unknown key' error, but got no error")) ]))
                                  .skip)
                                (.seq
                                  .skip
                                  (.ifte
                                    (.unop
                                      "!"
                                      (.call
                                        "Contains"
                                        [(.call "Error" []), (.name "unknownError")]))
                                    (.expr
                                      (.call
                                        "Errorf"
                                        [ (.lit (.str "expected '%s', but got '%s'"))
                                        , (.name "unknownError")
                                        , (.call "Error" []) ]))
                                    .skip))))))))))))) }

/-- `envconfig.TestUsageBadFormat`  (from `usage_test.go`) -/
def f_envconfig_TestUsageBadFormat : Func :=
  { name := "envconfig.TestUsageBadFormat"
  , params := ["t"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.name "s"))
              (.seq
                (.expr (.call "Clearenv" []))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "buf"
                      (.mcall (.name "bytes") "Buffer" [(.field (.name "bytes") "Buffer")]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "err"
                          (.call
                            "envconfig.Usagef"
                            [ (.lit (.str "env_config"))
                            , (.hole "op:addressOf")
                            , (.name "buf")
                            , (.lit (.str "{{range .}}{.Key}\\n{{end}}")) ]))
                        (.seq
                          .skip
                          (.seq
                            (.ifte
                              (.binop "!=" (.name "err") (.name "nil"))
                              (.expr (.call "Error" [(.call "Error" [])]))
                              .skip)
                            (.expr
                              (.mcall
                                (.name "envconfig")
                                "testUsageBadFormatResult"
                                [ (.field (.name "envconfig") "testUsageBadFormatResult")
                                , (.call "String" [])
                                , (.name "t") ]))))))))))) }

/-- `usage_test.go:envconfig.usage_test.go`  (from `usage_test.go`) -/
def f_usage_test_go_envconfig_usage_test_go : Func :=
  { name := "usage_test.go:envconfig.usage_test.go"
  , params := []
  , body := (.seq
            (.hole "stmt:IMPORT")
            (.seq
              (.hole "stmt:IMPORT")
              (.seq
                (.hole "stmt:IMPORT")
                (.seq
                  (.hole "stmt:IMPORT")
                  (.seq
                    (.hole "stmt:IMPORT")
                    (.seq (.hole "stmt:IMPORT") (.seq (.hole "stmt:IMPORT") (.hole "stmt:IMPORT")))))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_envconfig_clinit_,
  f_env_os_go_envconfig_env_os_go,
  f_env_syscall_go_envconfig_env_syscall_go,
  f_envconfig_ParseError_Error,
  f_envconfig_gatherInfo,
  f_envconfig_CheckDisallowed,
  f_envconfig_Process,
  f_envconfig_MustProcess,
  f_envconfig_processField,
  f_envconfig_interfaceFrom,
  f_envconfig_decoderFrom__lambda_0,
  f_envconfig_decoderFrom,
  f_envconfig_setterFrom__lambda_1,
  f_envconfig_setterFrom,
  f_envconfig_textUnmarshaler__lambda_2,
  f_envconfig_textUnmarshaler,
  f_envconfig_binaryUnmarshaler__lambda_3,
  f_envconfig_binaryUnmarshaler,
  f_envconfig_isTrue,
  f_envconfig_go_envconfig_envconfig_go,
  f_envconfig_TestParseURL,
  f_envconfig_TestParseURLError,
  f_envconfig_1_8_test_go_envconfig_envconfig_1_8_test_go,
  f_envconfig_HonorDecodeInStruct_Decode,
  f_envconfig_CustomURL_UnmarshalBinary,
  f_envconfig_TestProcess,
  f_envconfig_TestParseErrorBool,
  f_envconfig_TestParseErrorFloat32,
  f_envconfig_TestParseErrorInt,
  f_envconfig_TestParseErrorUint,
  f_envconfig_TestParseErrorSplitWords,
  f_envconfig_TestErrInvalidSpecification,
  f_envconfig_TestUnsetVars,
  f_envconfig_TestAlternateVarNames,
  f_envconfig_TestRequiredVar,
  f_envconfig_TestRequiredMissing,
  f_envconfig_TestBlankDefaultVar,
  f_envconfig_TestNonBlankDefaultVar,
  f_envconfig_TestExplicitBlankDefaultVar,
  f_envconfig_TestAlternateNameDefaultVar,
  f_envconfig_TestRequiredDefault,
  f_envconfig_TestPointerFieldBlank,
  f_envconfig_TestEmptyMapFieldOverride,
  f_envconfig_TestMustProcess,
  f_envconfig_TestEmbeddedStruct,
  f_envconfig_TestEmbeddedButIgnoredStruct,
  f_envconfig_TestNonPointerFailsProperly,
  f_envconfig_TestCustomValueFields,
  f_envconfig_TestCustomPointerFields,
  f_envconfig_TestEmptyPrefixUsesFieldNames,
  f_envconfig_TestNestedStructVarName,
  f_envconfig_TestTextUnmarshalerError,
  f_envconfig_TestBinaryUnmarshalerError,
  f_envconfig_TestCheckDisallowedOnlyAllowed,
  f_envconfig_TestCheckDisallowedMispelled,
  f_envconfig_TestCheckDisallowedIgnored,
  f_envconfig_TestErrorMessageForRequiredAltVar,
  f_envconfig_bracketed_Set,
  f_envconfig_bracketed_String,
  f_envconfig_quoted_Decode,
  f_envconfig_setterStruct_Set,
  f_envconfig_BenchmarkGatherInfo,
  f_envconfig_test_go_envconfig_envconfig_test_go,
  f_envconfig_implementsInterface,
  f_envconfig_toTypeDescription,
  f_envconfig_Usage,
  f_envconfig_Usagef__lambda_0,
  f_envconfig_Usagef__lambda_1,
  f_envconfig_Usagef__lambda_2,
  f_envconfig_Usagef__lambda_3,
  f_envconfig_Usagef__lambda_4,
  f_envconfig_Usagef,
  f_envconfig_Usaget,
  f_usage_go_envconfig_usage_go,
  f_envconfig_TestMain,
  f_envconfig_compareUsage,
  f_envconfig_TestUsageDefault,
  f_envconfig_TestUsageTable,
  f_envconfig_TestUsageList,
  f_envconfig_TestUsageCustomFormat,
  f_envconfig_TestUsageUnknownKeyFormat,
  f_envconfig_TestUsageBadFormat,
  f_usage_test_go_envconfig_usage_test_go
] }

end Autoform.Generated