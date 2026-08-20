import Autoform.Lang.Core.Semantics

/-!
# LangJava — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `com.google.gson.internal.ConstructorConstructor.<init>:void(java.util.Map,boolean,java.util.List)`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor__init__void_java_util_Map_boolean_java_util_List_ : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.<init>:void(java.util.Map,boolean,java.util.List)"
  , params := ["this", "instanceCreators", "useJdkUnsafe", "reflectionFilters"]
  , body := (.seq
            (.setField (.name "this") "instanceCreators" (.name "instanceCreators"))
            (.seq
              (.setField (.name "this") "useJdkUnsafe" (.name "useJdkUnsafe"))
              (.setField (.name "this") "reflectionFilters" (.name "reflectionFilters")))) }

/-- `com.google.gson.internal.ConstructorConstructor.checkInstantiable:java.lang.String(java.lang.Class)`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_checkInstantiable_java_lang_String_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.checkInstantiable:java.lang.String(java.lang.Class)"
  , params := ["c"]
  , body := (.seq
            .skip
            (.seq
              (.assign "modifiers" (.call "getModifiers" []))
              (.seq
                (.ifte
                  (.call "isInterface" [(.name "modifiers")])
                  (.ret
                    (.binop
                      "+"
                      (.binop
                        "+"
                        (.lit
                          (.str "Interfaces can't be instantiated! Register an InstanceCreator"))
                        (.lit (.str " or a TypeAdapter for this type. Interface name: ")))
                      (.call "getName" [])))
                  .skip)
                (.seq
                  (.ifte
                    (.call "isAbstract" [(.name "modifiers")])
                    (.ret
                      (.binop
                        "+"
                        (.binop
                          "+"
                          (.binop
                            "+"
                            (.binop
                              "+"
                              (.lit
                                (.str "Abstract classes can't be instantiated! Adjust the R8 configuration or register"))
                              (.lit
                                (.str " an InstanceCreator or a TypeAdapter for this type. Class name: ")))
                            (.call "getName" []))
                          (.lit (.str "\\nSee ")))
                        (.call
                          "com.google.gson.internal.TroubleshootingGuide.createUrl:java.lang.String(java.lang.String)"
                          [(.lit (.str "r8-abstract-class"))])))
                    .skip)
                  (.ret (.lit .unit)))))) }

/-- `com.google.gson.internal.ConstructorConstructor.get:com.google.gson.internal.ObjectConstructor(com.google.gson.reflect.TypeToken)`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_get_com_google_gson_internal_ObjectConstructor_com_google_gson_reflect : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.get:com.google.gson.internal.ObjectConstructor(com.google.gson.reflect.TypeToken)"
  , params := ["this", "typeToken"]
  , body := (.ret
            (.call
              "com.google.gson.internal.ConstructorConstructor.get:com.google.gson.internal.ObjectConstructor(com.google.gson.reflect.TypeToken,boolean)"
              [(.name "typeToken"), (.lit (.bool true))])) }

/-- `com.google.gson.internal.ConstructorConstructor.get:com.google.gson.internal.ObjectConstructor(com.google.gson.reflect.TypeToken,boolean)`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_get_com_google_gson_internal_ObjectConstructor_com_google_gson_reflect' : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.get:com.google.gson.internal.ObjectConstructor(com.google.gson.reflect.TypeToken,boolean)"
  , params := ["this", "typeToken", "allowUnsafe"]
  , body := (.seq
            .skip
            (.seq
              (.assign "type" (.call "getType" []))
              (.seq
                .skip
                (.seq
                  (.assign "rawType" (.call "getRawType" []))
                  (.seq
                    .skip
                    (.seq
                      (.assign "typeCreator" (.hole "op:cast"))
                      (.seq
                        (.ifte
                          (.binop "!=" (.name "typeCreator") (.lit .unit))
                          (.seq
                            .skip
                            (.seq
                              (.assign "$obj0" (.hole "op:alloc"))
                              (.seq
                                (.expr
                                  (.call
                                    "com.google.gson.internal.ConstructorConstructor$InstanceCreatorConstructor.<init>:void(com.google.gson.InstanceCreator,java.lang.reflect.Type)"
                                    [(.name "typeCreator"), (.name "type")]))
                                (.ret (.name "$obj0")))))
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.assign "rawTypeCreator" (.hole "op:cast"))
                            (.seq
                              (.ifte
                                (.binop "!=" (.name "rawTypeCreator") (.lit .unit))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "$obj1" (.hole "op:alloc"))
                                    (.seq
                                      (.expr
                                        (.call
                                        "com.google.gson.internal.ConstructorConstructor$InstanceCreatorConstructor.<init>:void(com.google.gson.InstanceCreator,java.lang.reflect.Type)"
                                        [(.name "rawTypeCreator"), (.name "type")]))
                                      (.ret (.name "$obj1")))))
                                .skip)
                              (.seq
                                .skip
                                (.seq
                                  (.assign
                                    "specialConstructor"
                                    (.call
                                      "com.google.gson.internal.ConstructorConstructor.newSpecialCollectionConstructor:com.google.gson.internal.ObjectConstructor(java.lang.reflect.Type,java.lang.Class)"
                                      [(.name "type"), (.name "rawType")]))
                                  (.seq
                                    (.ifte
                                      (.binop "!=" (.name "specialConstructor") (.lit .unit))
                                      (.ret (.name "specialConstructor"))
                                      .skip)
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "filterResult"
                                        (.call
                                        "com.google.gson.internal.ReflectionAccessFilterHelper.getFilterResult:com.google.gson.ReflectionAccessFilter.FilterResult(java.util.List,java.lang.Class)"
                                        [ (.field (.name "this") "reflectionFilters")
                                        , (.name "rawType") ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "defaultConstructor"
                                        (.call
                                        "com.google.gson.internal.ConstructorConstructor.newDefaultConstructor:com.google.gson.internal.ObjectConstructor(java.lang.Class,com.google.gson.ReflectionAccessFilter.FilterResult)"
                                        [(.name "rawType"), (.name "filterResult")]))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "defaultConstructor") (.lit .unit))
                                        (.ret (.name "defaultConstructor"))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "defaultImplementation"
                                        (.call
                                        "com.google.gson.internal.ConstructorConstructor.newDefaultImplementationConstructor:com.google.gson.internal.ObjectConstructor(java.lang.Class)"
                                        [(.name "rawType")]))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "defaultImplementation") (.lit .unit))
                                        (.ret (.name "defaultImplementation"))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "exceptionMessage"
                                        (.call
                                        "com.google.gson.internal.ConstructorConstructor.checkInstantiable:java.lang.String(java.lang.Class)"
                                        [(.name "rawType")]))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "exceptionMessage") (.lit .unit))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "$obj2" (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.ConstructorConstructor$ThrowingObjectConstructor.<init>:void(java.lang.String)"
                                        [(.name "exceptionMessage")]))
                                        (.ret (.name "$obj2")))))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.unop "!" (.name "allowUnsafe"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "message"
                                        (.binop
                                        "+"
                                        (.binop
                                        "+"
                                        (.lit (.str "Unable to create instance of "))
                                        (.name "rawType"))
                                        (.lit
                                        (.str "; Register an InstanceCreator or a TypeAdapter for this type."))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "$obj3" (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.ConstructorConstructor$ThrowingObjectConstructor.<init>:void(java.lang.String)"
                                        [(.name "message")]))
                                        (.ret (.name "$obj3")))))))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.name "filterResult")
                                        (.field (.name "FilterResult") "ALLOW"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "message"
                                        (.binop
                                        "+"
                                        (.binop
                                        "+"
                                        (.binop
                                        "+"
                                        (.binop
                                        "+"
                                        (.lit (.str "Unable to create instance of "))
                                        (.name "rawType"))
                                        (.lit
                                        (.str "; ReflectionAccessFilter does not permit using reflection or Unsafe. Register an")))
                                        (.lit
                                        (.str " InstanceCreator or a TypeAdapter for this type or adjust the access filter to")))
                                        (.lit (.str " allow using reflection."))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "$obj4" (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.ConstructorConstructor$ThrowingObjectConstructor.<init>:void(java.lang.String)"
                                        [(.name "message")]))
                                        (.ret (.name "$obj4")))))))
                                        .skip)
                                        (.ret
                                        (.call
                                        "com.google.gson.internal.ConstructorConstructor.newUnsafeAllocator:com.google.gson.internal.ObjectConstructor(java.lang.Class)"
                                        [(.name "rawType")])))))))))))))))))))))))))))) }

/-- `com.google.gson.internal.ConstructorConstructor.newSpecialCollectionConstructor:com.google.gson.internal.ObjectConstructor(java.lang.reflect.Type,java.lang.Class)`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_newSpecialCollectionConstructor_com_google_gson_internal_ObjectConstru : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.newSpecialCollectionConstructor:com.google.gson.internal.ObjectConstructor(java.lang.reflect.Type,java.lang.Class)"
  , params := ["type", "rawType"]
  , body := (.seq
            (.ifte
              (.mcall (.name "EnumSet") "class" [(.name "rawType")])
              (.ret
                (.fnref
                  "com.google.gson.internal.ConstructorConstructor.<lambda>0:java.lang.Object()"))
              (.ifte
                (.binop "==" (.name "rawType") (.field (.name "EnumMap") "class"))
                (.ret
                  (.fnref
                    "com.google.gson.internal.ConstructorConstructor.<lambda>1:java.lang.Object()"))
                .skip))
            (.ret (.lit .unit))) }

/-- `com.google.gson.internal.ConstructorConstructor.newDefaultConstructor:com.google.gson.internal.ObjectConstructor(java.lang.Class,com.google.gson.ReflectionAccessFilter.FilterResult)`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_newDefaultConstructor_com_google_gson_internal_ObjectConstructor_java_ : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.newDefaultConstructor:com.google.gson.internal.ObjectConstructor(java.lang.Class,com.google.gson.ReflectionAccessFilter.FilterResult)"
  , params := ["rawType", "filterResult"]
  , body := (.seq
            (.ifte (.call "isAbstract" [(.call "getModifiers" [])]) (.ret (.lit .unit)) .skip)
            (.seq
              .skip
              (.seq
                (.tryCatch
                  (.assign
                    "constructor"
                    (.call "getDeclaredConstructor" [(.hole "op:arrayInitializer")]))
                  "__exc"
                  (.ret (.lit .unit)))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "canAccess"
                      (.binop
                        "||"
                        (.binop "==" (.name "filterResult") (.field (.name "FilterResult") "ALLOW"))
                        (.binop
                          "&&"
                          (.call
                            "com.google.gson.internal.ReflectionAccessFilterHelper.canAccess:boolean(java.lang.reflect.AccessibleObject,java.lang.Object)"
                            [(.name "constructor"), (.lit .unit)])
                          (.binop
                            "||"
                            (.binop
                              "!="
                              (.name "filterResult")
                              (.field (.name "FilterResult") "BLOCK_ALL"))
                            (.call "isPublic" [(.call "getModifiers" [])])))))
                    (.seq
                      (.ifte
                        (.unop "!" (.name "canAccess"))
                        (.seq
                          .skip
                          (.seq
                            (.assign
                              "message"
                              (.binop
                                "+"
                                (.binop
                                  "+"
                                  (.binop
                                    "+"
                                    (.binop
                                      "+"
                                      (.binop
                                        "+"
                                        (.lit (.str "Unable to invoke no-args constructor of "))
                                        (.name "rawType"))
                                      (.lit (.str ";")))
                                    (.lit
                                      (.str " constructor is not accessible and ReflectionAccessFilter does not permit making")))
                                  (.lit
                                    (.str " it accessible. Register an InstanceCreator or a TypeAdapter for this type, change")))
                                (.lit
                                  (.str " the visibility of the constructor or adjust the access filter."))))
                            (.seq
                              .skip
                              (.seq
                                (.assign "$obj10" (.hole "op:alloc"))
                                (.seq
                                  (.expr
                                    (.call
                                      "com.google.gson.internal.ConstructorConstructor$ThrowingObjectConstructor.<init>:void(java.lang.String)"
                                      [(.name "message")]))
                                  (.ret (.name "$obj10")))))))
                        .skip)
                      (.seq
                        (.ifte
                          (.binop
                            "=="
                            (.name "filterResult")
                            (.field (.name "FilterResult") "ALLOW"))
                          (.seq
                            .skip
                            (.seq
                              (.assign
                                "exceptionMessage"
                                (.call
                                  "com.google.gson.internal.reflect.ReflectionHelper.tryMakeAccessible:java.lang.String(java.lang.reflect.Constructor)"
                                  [(.name "constructor")]))
                              (.ifte
                                (.binop "!=" (.name "exceptionMessage") (.lit .unit))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "$obj11" (.hole "op:alloc"))
                                    (.seq
                                      (.expr
                                        (.call
                                        "com.google.gson.internal.ConstructorConstructor$ThrowingObjectConstructor.<init>:void(java.lang.String)"
                                        [(.name "exceptionMessage")]))
                                      (.ret (.name "$obj11")))))
                                .skip)))
                          .skip)
                        (.ret
                          (.fnref
                            "com.google.gson.internal.ConstructorConstructor.<lambda>2:java.lang.Object()"))))))))) }

/-- `com.google.gson.internal.ConstructorConstructor.newDefaultImplementationConstructor:com.google.gson.internal.ObjectConstructor(java.lang.Class)`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_newDefaultImplementationConstructor_com_google_gson_internal_ObjectCon : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.newDefaultImplementationConstructor:com.google.gson.internal.ObjectConstructor(java.lang.Class)"
  , params := ["rawType"]
  , body := (.seq
            (.ifte
              (.mcall (.name "Collection") "class" [(.name "rawType")])
              (.seq
                .skip
                (.seq (.assign "constructor" (.hole "op:cast")) (.ret (.name "constructor"))))
              .skip)
            (.seq
              (.ifte
                (.mcall (.name "Map") "class" [(.name "rawType")])
                (.seq
                  .skip
                  (.seq (.assign "constructor" (.hole "op:cast")) (.ret (.name "constructor"))))
                .skip)
              (.ret (.lit .unit)))) }

/-- `com.google.gson.internal.ConstructorConstructor.newCollectionConstructor:com.google.gson.internal.ObjectConstructor(java.lang.Class)`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_newCollectionConstructor_com_google_gson_internal_ObjectConstructor_ja : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.newCollectionConstructor:com.google.gson.internal.ObjectConstructor(java.lang.Class)"
  , params := ["rawType"]
  , body := (.seq
            (.ifte
              (.call "isAssignableFrom" [(.field (.name "ArrayList") "class")])
              (.ret (.fnref "java.util.ArrayList.new:<unresolvedSignature>"))
              (.ifte
                (.call "isAssignableFrom" [(.field (.name "LinkedHashSet") "class")])
                (.ret (.fnref "java.util.LinkedHashSet.new:<unresolvedSignature>"))
                (.ifte
                  (.call "isAssignableFrom" [(.field (.name "TreeSet") "class")])
                  (.ret (.fnref "java.util.TreeSet.new:<unresolvedSignature>"))
                  (.ifte
                    (.call "isAssignableFrom" [(.field (.name "ArrayDeque") "class")])
                    (.ret (.fnref "java.util.ArrayDeque.new:<unresolvedSignature>"))
                    .skip))))
            (.ret (.lit .unit))) }

/-- `com.google.gson.internal.ConstructorConstructor.newMapConstructor:com.google.gson.internal.ObjectConstructor(java.lang.Class)`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_newMapConstructor_com_google_gson_internal_ObjectConstructor_java_lang : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.newMapConstructor:com.google.gson.internal.ObjectConstructor(java.lang.Class)"
  , params := ["rawType"]
  , body := (.seq
            (.ifte
              (.call "isAssignableFrom" [(.field (.name "LinkedHashMap") "class")])
              (.ret (.fnref "java.util.LinkedHashMap.new:<unresolvedSignature>"))
              (.ifte
                (.call "isAssignableFrom" [(.field (.name "TreeMap") "class")])
                (.ret (.fnref "java.util.TreeMap.new:<unresolvedSignature>"))
                (.ifte
                  (.call "isAssignableFrom" [(.field (.name "ConcurrentHashMap") "class")])
                  (.ret (.fnref "java.util.concurrent.ConcurrentHashMap.new:<unresolvedSignature>"))
                  (.ifte
                    (.call "isAssignableFrom" [(.field (.name "ConcurrentSkipListMap") "class")])
                    (.ret
                      (.fnref
                        "java.util.concurrent.ConcurrentSkipListMap.new:<unresolvedSignature>"))
                    .skip))))
            (.ret (.lit .unit))) }

/-- `com.google.gson.internal.ConstructorConstructor.newUnsafeAllocator:com.google.gson.internal.ObjectConstructor(java.lang.Class)`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_newUnsafeAllocator_com_google_gson_internal_ObjectConstructor_java_lan : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.newUnsafeAllocator:com.google.gson.internal.ObjectConstructor(java.lang.Class)"
  , params := ["this", "rawType"]
  , body := (.ifte
            (.field (.name "this") "useJdkUnsafe")
            (.ret
              (.fnref
                "com.google.gson.internal.ConstructorConstructor.<lambda>3:java.lang.Object()"))
            (.seq
              .skip
              (.seq
                (.assign
                  "exceptionMessage"
                  (.binop
                    "+"
                    (.binop
                      "+"
                      (.binop
                        "+"
                        (.binop "+" (.lit (.str "Unable to create instance of ")) (.name "rawType"))
                        (.lit
                          (.str "; usage of JDK Unsafe is disabled. Registering an InstanceCreator or a TypeAdapter")))
                      (.lit
                        (.str " for this type, adding a no-args constructor, or enabling usage of JDK Unsafe may")))
                    (.lit (.str " fix this problem."))))
                (.seq
                  (.ifte
                    (.binop "==" (.hole "op:sizeOf") (.lit (.int 0)))
                    (.assign
                      "exceptionMessage"
                      (.binop
                        "+"
                        (.name "exceptionMessage")
                        (.lit
                          (.str " Or adjust your R8 configuration to keep the no-args constructor of the class."))))
                    .skip)
                  (.seq
                    .skip
                    (.seq
                      (.assign "$obj15" (.hole "op:alloc"))
                      (.seq
                        (.expr
                          (.call
                            "com.google.gson.internal.ConstructorConstructor$ThrowingObjectConstructor.<init>:void(java.lang.String)"
                            [(.name "exceptionMessage")]))
                        (.ret (.name "$obj15"))))))))) }

/-- `com.google.gson.internal.ConstructorConstructor.toString:java.lang.String()`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_toString_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.toString:java.lang.String()"
  , params := ["this"]
  , body := (.ret (.mcall (.name "this") "instanceCreators" [])) }

/-- `com.google.gson.internal.ConstructorConstructor$ThrowingObjectConstructor.<init>:void(java.lang.String)`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_ThrowingObjectConstructor__init__void_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor$ThrowingObjectConstructor.<init>:void(java.lang.String)"
  , params := ["this", "exceptionMessage"]
  , body := (.setField (.name "this") "exceptionMessage" (.name "exceptionMessage")) }

/-- `com.google.gson.internal.ConstructorConstructor$ThrowingObjectConstructor.construct:java.lang.Object()`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_ThrowingObjectConstructor_construct_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor$ThrowingObjectConstructor.construct:java.lang.Object()"
  , params := ["this"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.ConstructorConstructor$InstanceCreatorConstructor.<init>:void(com.google.gson.InstanceCreator,java.lang.reflect.Type)`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_InstanceCreatorConstructor__init__void_com_google_gson_InstanceCreator : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor$InstanceCreatorConstructor.<init>:void(com.google.gson.InstanceCreator,java.lang.reflect.Type)"
  , params := ["this", "instanceCreator", "type"]
  , body := (.seq
            (.setField (.name "this") "instanceCreator" (.name "instanceCreator"))
            (.setField (.name "this") "type" (.name "type"))) }

/-- `com.google.gson.internal.ConstructorConstructor$InstanceCreatorConstructor.construct:java.lang.Object()`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor_InstanceCreatorConstructor_construct_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor$InstanceCreatorConstructor.construct:java.lang.Object()"
  , params := ["this"]
  , body := (.ret (.mcall (.name "this") "instanceCreator" [(.field (.name "this") "type")])) }

/-- `com.google.gson.internal.ConstructorConstructor.<lambda>0:java.lang.Object()`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor__lambda_0_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.<lambda>0:java.lang.Object()"
  , params := []
  , body := (.seq
            .skip
            (.ifte
              (.hole "op:instanceOf")
              (.seq
                .skip
                (.seq
                  (.assign
                    "elementType"
                    (.index (.call "getActualTypeArguments" []) (.lit (.int 0))))
                  (.ifte
                    (.hole "op:instanceOf")
                    (.seq .skip (.seq (.assign "set" (.hole "op:cast")) (.ret (.name "set"))))
                    (.hole "control:THROW"))))
              (.hole "control:THROW"))) }

/-- `com.google.gson.internal.ConstructorConstructor.<lambda>1:java.lang.Object()`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor__lambda_1_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.<lambda>1:java.lang.Object()"
  , params := []
  , body := (.seq
            .skip
            (.ifte
              (.hole "op:instanceOf")
              (.seq
                .skip
                (.seq
                  (.assign
                    "elementType"
                    (.index (.call "getActualTypeArguments" []) (.lit (.int 0))))
                  (.ifte
                    (.hole "op:instanceOf")
                    (.seq .skip (.seq (.assign "map" (.hole "op:cast")) (.ret (.name "map"))))
                    (.hole "control:THROW"))))
              (.hole "control:THROW"))) }

/-- `com.google.gson.internal.ConstructorConstructor.<lambda>2:java.lang.Object()`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor__lambda_2_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.<lambda>2:java.lang.Object()"
  , params := []
  , body := (.seq .skip (.hole "control:TRY-multiCatch")) }

/-- `com.google.gson.internal.ConstructorConstructor.<lambda>3:java.lang.Object()`  (from `internal/ConstructorConstructor.java`) -/
def f_com_google_gson_internal_ConstructorConstructor__lambda_3_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.ConstructorConstructor.<lambda>3:java.lang.Object()"
  , params := []
  , body := (.seq
            .skip
            (.tryCatch
              (.seq
                .skip
                (.seq (.assign "newInstance" (.hole "op:cast")) (.ret (.name "newInstance"))))
              "__exc"
              (.hole "control:THROW"))) }

/-- `com.google.gson.internal.Excluder.clone:com.google.gson.internal.Excluder()`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_clone_com_google_gson_internal_Excluder__ : Func :=
  { name := "com.google.gson.internal.Excluder.clone:com.google.gson.internal.Excluder()"
  , params := ["this"]
  , body := (.tryCatch (.ret (.hole "op:cast")) "__exc" (.hole "control:THROW")) }

/-- `com.google.gson.internal.Excluder.withVersion:com.google.gson.internal.Excluder(double)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_withVersion_com_google_gson_internal_Excluder_double_ : Func :=
  { name := "com.google.gson.internal.Excluder.withVersion:com.google.gson.internal.Excluder(double)"
  , params := ["this", "ignoreVersionsAfter"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "result"
                (.call
                  "com.google.gson.internal.Excluder.clone:com.google.gson.internal.Excluder()"
                  []))
              (.seq
                (.setField (.name "result") "version" (.name "ignoreVersionsAfter"))
                (.ret (.name "result"))))) }

/-- `com.google.gson.internal.Excluder.withModifiers:com.google.gson.internal.Excluder(int[])`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_withModifiers_com_google_gson_internal_Excluder_int___ : Func :=
  { name := "com.google.gson.internal.Excluder.withModifiers:com.google.gson.internal.Excluder(int[])"
  , params := ["this", "modifiers"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "result"
                (.call
                  "com.google.gson.internal.Excluder.clone:com.google.gson.internal.Excluder()"
                  []))
              (.seq
                (.setField (.name "result") "modifiers" (.lit (.int 0)))
                (.seq (.hole "control:FOR") (.ret (.name "result")))))) }

/-- `com.google.gson.internal.Excluder.disableInnerClassSerialization:com.google.gson.internal.Excluder()`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_disableInnerClassSerialization_com_google_gson_internal_Excluder__ : Func :=
  { name := "com.google.gson.internal.Excluder.disableInnerClassSerialization:com.google.gson.internal.Excluder()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "result"
                (.call
                  "com.google.gson.internal.Excluder.clone:com.google.gson.internal.Excluder()"
                  []))
              (.seq
                (.setField (.name "result") "serializeInnerClasses" (.lit (.bool false)))
                (.ret (.name "result"))))) }

/-- `com.google.gson.internal.Excluder.excludeFieldsWithoutExposeAnnotation:com.google.gson.internal.Excluder()`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_excludeFieldsWithoutExposeAnnotation_com_google_gson_internal_Excluder__ : Func :=
  { name := "com.google.gson.internal.Excluder.excludeFieldsWithoutExposeAnnotation:com.google.gson.internal.Excluder()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "result"
                (.call
                  "com.google.gson.internal.Excluder.clone:com.google.gson.internal.Excluder()"
                  []))
              (.seq
                (.setField (.name "result") "requireExpose" (.lit (.bool true)))
                (.ret (.name "result"))))) }

/-- `com.google.gson.internal.Excluder.withExclusionStrategy:com.google.gson.internal.Excluder(com.google.gson.ExclusionStrategy,boolean,boolean)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_withExclusionStrategy_com_google_gson_internal_Excluder_com_google_gson_ExclusionStr : Func :=
  { name := "com.google.gson.internal.Excluder.withExclusionStrategy:com.google.gson.internal.Excluder(com.google.gson.ExclusionStrategy,boolean,boolean)"
  , params := ["this", "exclusionStrategy", "serialization", "deserialization"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "result"
                (.call
                  "com.google.gson.internal.Excluder.clone:com.google.gson.internal.Excluder()"
                  []))
              (.seq
                (.ifte
                  (.name "serialization")
                  (.seq
                    (.setField (.name "result") "serializationStrategies" (.hole "op:alloc"))
                    (.seq
                      (.expr
                        (.mcall
                          (.name "result")
                          "serializationStrategies"
                          [(.field (.name "this") "serializationStrategies")]))
                      (.expr
                        (.mcall
                          (.name "result")
                          "serializationStrategies"
                          [(.name "exclusionStrategy")]))))
                  .skip)
                (.seq
                  (.ifte
                    (.name "deserialization")
                    (.seq
                      (.setField (.name "result") "deserializationStrategies" (.hole "op:alloc"))
                      (.seq
                        (.expr
                          (.mcall
                            (.name "result")
                            "deserializationStrategies"
                            [(.field (.name "this") "deserializationStrategies")]))
                        (.expr
                          (.mcall
                            (.name "result")
                            "deserializationStrategies"
                            [(.name "exclusionStrategy")]))))
                    .skip)
                  (.ret (.name "result")))))) }

/-- `com.google.gson.internal.Excluder.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_create_com_google_gson_TypeAdapter_com_google_gson_Gson_com_google_gson_reflect_Type : Func :=
  { name := "com.google.gson.internal.Excluder.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "type"]
  , body := (.seq
            .skip
            (.seq
              (.assign "rawType" (.call "getRawType" []))
              (.seq
                .skip
                (.seq
                  (.assign
                    "skipSerialize"
                    (.call
                      "com.google.gson.internal.Excluder.excludeClass:boolean(java.lang.Class,boolean)"
                      [(.name "rawType"), (.lit (.bool true))]))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "skipDeserialize"
                        (.call
                          "com.google.gson.internal.Excluder.excludeClass:boolean(java.lang.Class,boolean)"
                          [(.name "rawType"), (.lit (.bool false))]))
                      (.seq
                        (.ifte
                          (.binop
                            "&&"
                            (.unop "!" (.name "skipSerialize"))
                            (.unop "!" (.name "skipDeserialize")))
                          (.ret (.lit .unit))
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.assign "$obj1" (.hole "op:alloc"))
                            (.seq
                              (.expr
                                (.call
                                  "com.google.gson.internal.Excluder.create.TypeAdapter$0.<init>:void()"
                                  [ (.name "this")
                                  , (.name "skipDeserialize")
                                  , (.name "skipSerialize")
                                  , (.name "gson")
                                  , (.name "type") ]))
                              (.ret (.name "$obj1")))))))))))) }

/-- `com.google.gson.internal.Excluder.excludeField:boolean(java.lang.reflect.Field,boolean)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_excludeField_boolean_java_lang_reflect_Field_boolean_ : Func :=
  { name := "com.google.gson.internal.Excluder.excludeField:boolean(java.lang.reflect.Field,boolean)"
  , params := ["this", "field", "serialize"]
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
                      (.call
                        "com.google.gson.internal.Excluder.isExcludedByModifier:boolean(java.lang.reflect.Field)"
                        [(.name "field")])
                      (.call
                        "com.google.gson.internal.Excluder.isExcludedByVersion:boolean(java.lang.reflect.Field)"
                        [(.name "field")]))
                    (.call "isSynthetic" []))
                  (.call
                    "com.google.gson.internal.Excluder.isExcludedByExposeAnnotation:boolean(java.lang.reflect.Field,boolean)"
                    [(.name "field"), (.name "serialize")]))
                (.call
                  "com.google.gson.internal.Excluder.excludeClass:boolean(java.lang.Class,boolean)"
                  [(.call "getType" []), (.name "serialize")]))
              (.call
                "com.google.gson.internal.Excluder.isExcludedByStrategy:boolean(java.lang.reflect.Field,boolean)"
                [(.name "field"), (.name "serialize")]))) }

/-- `com.google.gson.internal.Excluder.isExcludedByModifier:boolean(java.lang.reflect.Field)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_isExcludedByModifier_boolean_java_lang_reflect_Field_ : Func :=
  { name := "com.google.gson.internal.Excluder.isExcludedByModifier:boolean(java.lang.reflect.Field)"
  , params := ["this", "field"]
  , body := (.ret (.binop "!=" (.hole "op:and") (.lit (.int 0)))) }

/-- `com.google.gson.internal.Excluder.isExcludedByVersion:boolean(java.lang.reflect.Field)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_isExcludedByVersion_boolean_java_lang_reflect_Field_ : Func :=
  { name := "com.google.gson.internal.Excluder.isExcludedByVersion:boolean(java.lang.reflect.Field)"
  , params := ["this", "field"]
  , body := (.ret
            (.binop
              "&&"
              (.binop
                "!="
                (.field (.name "this") "version")
                (.field (.name "Excluder") "IGNORE_VERSIONS"))
              (.unop
                "!"
                (.call
                  "com.google.gson.internal.Excluder.isValidVersion:boolean(com.google.gson.annotations.Since,com.google.gson.annotations.Until)"
                  [ (.call "getAnnotation" [(.field (.name "Since") "class")])
                  , (.call "getAnnotation" [(.field (.name "Until") "class")]) ])))) }

/-- `com.google.gson.internal.Excluder.isExcludedByExposeAnnotation:boolean(java.lang.reflect.Field,boolean)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_isExcludedByExposeAnnotation_boolean_java_lang_reflect_Field_boolean_ : Func :=
  { name := "com.google.gson.internal.Excluder.isExcludedByExposeAnnotation:boolean(java.lang.reflect.Field,boolean)"
  , params := ["this", "field", "serialize"]
  , body := (.seq
            (.ifte
              (.unop "!" (.field (.name "this") "requireExpose"))
              (.ret (.lit (.bool false)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "annotation" (.call "getAnnotation" [(.field (.name "Expose") "class")]))
                (.ret
                  (.binop
                    "||"
                    (.binop "==" (.name "annotation") (.lit .unit))
                    (.cond
                      (.name "serialize")
                      (.unop "!" (.call "serialize" []))
                      (.unop "!" (.call "deserialize" [])))))))) }

/-- `com.google.gson.internal.Excluder.isExcludedByStrategy:boolean(java.lang.reflect.Field,boolean)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_isExcludedByStrategy_boolean_java_lang_reflect_Field_boolean_ : Func :=
  { name := "com.google.gson.internal.Excluder.isExcludedByStrategy:boolean(java.lang.reflect.Field,boolean)"
  , params := ["this", "field", "serialize"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "list"
                (.cond
                  (.name "serialize")
                  (.field (.name "this") "serializationStrategies")
                  (.field (.name "this") "deserializationStrategies")))
              (.seq
                (.ifte (.call "isEmpty" []) (.ret (.lit (.bool false))) .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "fieldAttributes" (.hole "op:alloc"))
                    (.seq
                      (.expr (.call "<init>" [(.name "field")]))
                      (.seq
                        .skip
                        (.seq
                          (.assign "$iterLocal0" (.call "iterator" []))
                          (.seq
                            (.loop
                              (.call "hasNext" [])
                              (.seq
                                .skip
                                (.seq
                                  (.assign "exclusionStrategy" (.call "next" []))
                                  (.ifte
                                    (.call "shouldSkipField" [(.name "fieldAttributes")])
                                    (.ret (.lit (.bool true)))
                                    .skip))))
                            (.ret (.lit (.bool false)))))))))))) }

/-- `com.google.gson.internal.Excluder.excludeClass:boolean(java.lang.Class,boolean)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_excludeClass_boolean_java_lang_Class_boolean_ : Func :=
  { name := "com.google.gson.internal.Excluder.excludeClass:boolean(java.lang.Class,boolean)"
  , params := ["this", "clazz", "serialize"]
  , body := (.seq
            (.ifte
              (.binop
                "&&"
                (.binop
                  "!="
                  (.field (.name "this") "version")
                  (.field (.name "Excluder") "IGNORE_VERSIONS"))
                (.unop
                  "!"
                  (.call
                    "com.google.gson.internal.Excluder.isValidVersion:boolean(com.google.gson.annotations.Since,com.google.gson.annotations.Until)"
                    [ (.call "getAnnotation" [(.field (.name "Since") "class")])
                    , (.call "getAnnotation" [(.field (.name "Until") "class")]) ])))
              (.ret (.lit (.bool true)))
              .skip)
            (.seq
              (.ifte
                (.binop
                  "&&"
                  (.unop "!" (.field (.name "this") "serializeInnerClasses"))
                  (.call
                    "com.google.gson.internal.Excluder.isInnerClass:boolean(java.lang.Class)"
                    [(.name "clazz")]))
                (.ret (.lit (.bool true)))
                .skip)
              (.seq
                (.ifte
                  (.binop
                    "&&"
                    (.binop
                      "&&"
                      (.unop "!" (.name "serialize"))
                      (.unop "!" (.mcall (.name "Enum") "class" [(.name "clazz")])))
                    (.call
                      "com.google.gson.internal.reflect.ReflectionHelper.isAnonymousOrNonStaticLocal:boolean(java.lang.Class)"
                      [(.name "clazz")]))
                  (.ret (.lit (.bool true)))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "list"
                      (.cond
                        (.name "serialize")
                        (.field (.name "this") "serializationStrategies")
                        (.field (.name "this") "deserializationStrategies")))
                    (.seq
                      .skip
                      (.seq
                        (.assign "$iterLocal1" (.call "iterator" []))
                        (.seq
                          (.loop
                            (.call "hasNext" [])
                            (.seq
                              .skip
                              (.seq
                                (.assign "exclusionStrategy" (.call "next" []))
                                (.ifte
                                  (.call "shouldSkipClass" [(.name "clazz")])
                                  (.ret (.lit (.bool true)))
                                  .skip))))
                          (.ret (.lit (.bool false))))))))))) }

/-- `com.google.gson.internal.Excluder.isInnerClass:boolean(java.lang.Class)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_isInnerClass_boolean_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.Excluder.isInnerClass:boolean(java.lang.Class)"
  , params := ["clazz"]
  , body := (.ret
            (.binop
              "&&"
              (.call "isMemberClass" [])
              (.unop
                "!"
                (.call
                  "com.google.gson.internal.reflect.ReflectionHelper.isStatic:boolean(java.lang.Class)"
                  [(.name "clazz")])))) }

/-- `com.google.gson.internal.Excluder.isValidVersion:boolean(com.google.gson.annotations.Since,com.google.gson.annotations.Until)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_isValidVersion_boolean_com_google_gson_annotations_Since_com_google_gson_annotations : Func :=
  { name := "com.google.gson.internal.Excluder.isValidVersion:boolean(com.google.gson.annotations.Since,com.google.gson.annotations.Until)"
  , params := ["this", "since", "until"]
  , body := (.ret
            (.binop
              "&&"
              (.call
                "com.google.gson.internal.Excluder.isValidSince:boolean(com.google.gson.annotations.Since)"
                [(.name "since")])
              (.call
                "com.google.gson.internal.Excluder.isValidUntil:boolean(com.google.gson.annotations.Until)"
                [(.name "until")]))) }

/-- `com.google.gson.internal.Excluder.isValidSince:boolean(com.google.gson.annotations.Since)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_isValidSince_boolean_com_google_gson_annotations_Since_ : Func :=
  { name := "com.google.gson.internal.Excluder.isValidSince:boolean(com.google.gson.annotations.Since)"
  , params := ["this", "annotation"]
  , body := (.seq
            (.ifte
              (.binop "!=" (.name "annotation") (.lit .unit))
              (.seq
                .skip
                (.seq
                  (.assign "annotationVersion" (.call "value" []))
                  (.ret (.binop ">=" (.field (.name "this") "version") (.name "annotationVersion")))))
              .skip)
            (.ret (.lit (.bool true)))) }

/-- `com.google.gson.internal.Excluder.isValidUntil:boolean(com.google.gson.annotations.Until)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_isValidUntil_boolean_com_google_gson_annotations_Until_ : Func :=
  { name := "com.google.gson.internal.Excluder.isValidUntil:boolean(com.google.gson.annotations.Until)"
  , params := ["this", "annotation"]
  , body := (.seq
            (.ifte
              (.binop "!=" (.name "annotation") (.lit .unit))
              (.seq
                .skip
                (.seq
                  (.assign "annotationVersion" (.call "value" []))
                  (.ret (.binop "<" (.field (.name "this") "version") (.name "annotationVersion")))))
              .skip)
            (.ret (.lit (.bool true)))) }

/-- `com.google.gson.internal.Excluder.<init>:void()`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder__init__void__ : Func :=
  { name := "com.google.gson.internal.Excluder.<init>:void()"
  , params := ["this"]
  , body := (.seq
            (.setField
              (.name "this")
              "version"
              (.field (.fnref "com.google.gson.internal.Excluder") "IGNORE_VERSIONS"))
            (.seq
              (.setField (.name "this") "modifiers" (.hole "op:or"))
              (.seq
                (.setField (.name "this") "serializeInnerClasses" (.lit (.bool true)))
                (.seq
                  (.setField (.name "this") "serializationStrategies" (.call "emptyList" []))
                  (.setField (.name "this") "deserializationStrategies" (.call "emptyList" [])))))) }

/-- `com.google.gson.internal.Excluder.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_Excluder__clinit__void__ : Func :=
  { name := "com.google.gson.internal.Excluder.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.Excluder")
              "IGNORE_VERSIONS"
              (.unop "-" (.hole "lit:unquoted")))
            (.seq
              (.setField (.fnref "com.google.gson.internal.Excluder") "DEFAULT" (.hole "op:alloc"))
              (.expr (.mcall (.fnref "com.google.gson.internal.Excluder") "DEFAULT" [])))) }

/-- `com.google.gson.internal.Excluder.create.TypeAdapter$0.read:java.lang.Object(com.google.gson.stream.JsonReader)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_create_TypeAdapter_0_read_java_lang_Object_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.Excluder.create.TypeAdapter$0.read:java.lang.Object(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.field (.name "this") "skipDeserialize")
              (.seq (.expr (.call "skipValue" [])) (.ret (.lit .unit)))
              .skip)
            (.ret (.call "read" [(.name "in")]))) }

/-- `com.google.gson.internal.Excluder.create.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_create_TypeAdapter_0_write_void_com_google_gson_stream_JsonWriter_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.Excluder.create.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.ifte
              (.field (.name "this") "skipSerialize")
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.expr (.call "write" [(.name "out"), (.name "value")]))) }

/-- `com.google.gson.internal.Excluder.create.TypeAdapter$0.delegate:com.google.gson.TypeAdapter()`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_create_TypeAdapter_0_delegate_com_google_gson_TypeAdapter__ : Func :=
  { name := "com.google.gson.internal.Excluder.create.TypeAdapter$0.delegate:com.google.gson.TypeAdapter()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "d" (.field (.name "this") "delegate"))
              (.seq
                (.ifte
                  (.binop "==" (.name "d") (.lit .unit))
                  (.assign "d" (.hole "op:assignment"))
                  .skip)
                (.ret (.name "d"))))) }

/-- `com.google.gson.internal.Excluder.create.TypeAdapter$0.<init>:void()`  (from `internal/Excluder.java`) -/
def f_com_google_gson_internal_Excluder_create_TypeAdapter_0__init__void__ : Func :=
  { name := "com.google.gson.internal.Excluder.create.TypeAdapter$0.<init>:void()"
  , params := ["this", "outerClass", "skipDeserialize", "skipSerialize", "gson", "type"]
  , body := (.seq
            (.setField (.name "this") "outerClass" (.name "outerClass"))
            (.seq
              (.setField (.name "this") "skipDeserialize" (.name "skipDeserialize"))
              (.seq
                (.setField (.name "this") "skipSerialize" (.name "skipSerialize"))
                (.seq
                  (.setField (.name "this") "gson" (.name "gson"))
                  (.setField (.name "this") "type" (.name "type")))))) }

/-- `com.google.gson.internal.GsonTypes.<init>:void()`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes__init__void__ : Func :=
  { name := "com.google.gson.internal.GsonTypes.<init>:void()"
  , params := ["this"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.GsonTypes.newParameterizedTypeWithOwner:java.lang.reflect.ParameterizedType(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type[])`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_newParameterizedTypeWithOwner_java_lang_reflect_ParameterizedType_java_lang_reflect : Func :=
  { name := "com.google.gson.internal.GsonTypes.newParameterizedTypeWithOwner:java.lang.reflect.ParameterizedType(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type[])"
  , params := ["ownerType", "rawType", "typeArguments"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj0" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.<init>:void(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type[])"
                    [(.name "ownerType"), (.name "rawType"), (.hole "op:arrayInitializer")]))
                (.ret (.name "$obj0"))))) }

/-- `com.google.gson.internal.GsonTypes.arrayOf:java.lang.reflect.GenericArrayType(java.lang.reflect.Type)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_arrayOf_java_lang_reflect_GenericArrayType_java_lang_reflect_Type_ : Func :=
  { name := "com.google.gson.internal.GsonTypes.arrayOf:java.lang.reflect.GenericArrayType(java.lang.reflect.Type)"
  , params := ["componentType"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj1" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.GsonTypes$GenericArrayTypeImpl.<init>:void(java.lang.reflect.Type)"
                    [(.name "componentType")]))
                (.ret (.name "$obj1"))))) }

/-- `com.google.gson.internal.GsonTypes.subtypeOf:java.lang.reflect.WildcardType(java.lang.reflect.Type)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_subtypeOf_java_lang_reflect_WildcardType_java_lang_reflect_Type_ : Func :=
  { name := "com.google.gson.internal.GsonTypes.subtypeOf:java.lang.reflect.WildcardType(java.lang.reflect.Type)"
  , params := ["bound"]
  , body := (.seq
            .skip
            (.seq
              (.ifte
                (.hole "op:instanceOf")
                (.assign "upperBounds" (.call "getUpperBounds" []))
                (.assign "upperBounds" (.hole "op:arrayInitializer")))
              (.seq
                .skip
                (.seq
                  (.assign "$obj2" (.hole "op:alloc"))
                  (.seq
                    (.expr
                      (.call
                        "com.google.gson.internal.GsonTypes$WildcardTypeImpl.<init>:void(java.lang.reflect.Type[],java.lang.reflect.Type[])"
                        [ (.name "upperBounds")
                        , (.field (.fnref "com.google.gson.internal.GsonTypes") "EMPTY_TYPE_ARRAY") ]))
                    (.ret (.name "$obj2"))))))) }

/-- `com.google.gson.internal.GsonTypes.supertypeOf:java.lang.reflect.WildcardType(java.lang.reflect.Type)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_supertypeOf_java_lang_reflect_WildcardType_java_lang_reflect_Type_ : Func :=
  { name := "com.google.gson.internal.GsonTypes.supertypeOf:java.lang.reflect.WildcardType(java.lang.reflect.Type)"
  , params := ["bound"]
  , body := (.seq
            .skip
            (.seq
              (.ifte
                (.hole "op:instanceOf")
                (.assign "lowerBounds" (.call "getLowerBounds" []))
                (.assign "lowerBounds" (.hole "op:arrayInitializer")))
              (.seq
                .skip
                (.seq
                  (.assign "$obj3" (.hole "op:alloc"))
                  (.seq
                    (.expr
                      (.call
                        "com.google.gson.internal.GsonTypes$WildcardTypeImpl.<init>:void(java.lang.reflect.Type[],java.lang.reflect.Type[])"
                        [(.hole "op:arrayInitializer"), (.name "lowerBounds")]))
                    (.ret (.name "$obj3"))))))) }

/-- `com.google.gson.internal.GsonTypes.canonicalize:java.lang.reflect.Type(java.lang.reflect.Type)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_canonicalize_java_lang_reflect_Type_java_lang_reflect_Type_ : Func :=
  { name := "com.google.gson.internal.GsonTypes.canonicalize:java.lang.reflect.Type(java.lang.reflect.Type)"
  , params := ["type"]
  , body := (.ifte
            (.hole "op:instanceOf")
            (.seq
              .skip
              (.seq
                (.assign "c" (.hole "op:cast"))
                (.ret (.cond (.call "isArray" []) (.hole "expr:BLOCK-impure") (.name "c")))))
            (.ifte
              (.hole "op:instanceOf")
              (.seq
                .skip
                (.seq
                  (.assign "p" (.hole "op:cast"))
                  (.seq
                    .skip
                    (.seq
                      (.assign "$obj5" (.hole "op:alloc"))
                      (.seq
                        (.expr
                          (.call
                            "com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.<init>:void(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type[])"
                            [ (.call "getOwnerType" [])
                            , (.hole "op:cast")
                            , (.hole "op:arrayInitializer") ]))
                        (.ret (.name "$obj5")))))))
              (.ifte
                (.hole "op:instanceOf")
                (.seq
                  .skip
                  (.seq
                    (.assign "g" (.hole "op:cast"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "$obj6" (.hole "op:alloc"))
                        (.seq
                          (.expr
                            (.call
                              "com.google.gson.internal.GsonTypes$GenericArrayTypeImpl.<init>:void(java.lang.reflect.Type)"
                              [(.call "getGenericComponentType" [])]))
                          (.ret (.name "$obj6")))))))
                (.ifte
                  (.hole "op:instanceOf")
                  (.seq
                    .skip
                    (.seq
                      (.assign "w" (.hole "op:cast"))
                      (.seq
                        .skip
                        (.seq
                          (.assign "$obj7" (.hole "op:alloc"))
                          (.seq
                            (.expr
                              (.call
                                "com.google.gson.internal.GsonTypes$WildcardTypeImpl.<init>:void(java.lang.reflect.Type[],java.lang.reflect.Type[])"
                                [(.call "getUpperBounds" []), (.call "getLowerBounds" [])]))
                            (.ret (.name "$obj7")))))))
                  (.ret (.name "type")))))) }

/-- `com.google.gson.internal.GsonTypes.getRawType:java.lang.Class(java.lang.reflect.Type)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_getRawType_java_lang_Class_java_lang_reflect_Type_ : Func :=
  { name := "com.google.gson.internal.GsonTypes.getRawType:java.lang.Class(java.lang.reflect.Type)"
  , params := ["type"]
  , body := (.ifte
            (.hole "op:instanceOf")
            (.ret (.hole "op:cast"))
            (.ifte
              (.hole "op:instanceOf")
              (.seq
                .skip
                (.seq
                  (.assign "parameterizedType" (.hole "op:cast"))
                  (.seq
                    .skip
                    (.seq (.assign "rawType" (.call "getRawType" [])) (.ret (.hole "op:cast"))))))
              (.ifte
                (.hole "op:instanceOf")
                (.seq
                  .skip
                  (.seq
                    (.assign "componentType" (.call "getGenericComponentType" []))
                    (.ret (.call "getClass" []))))
                (.ifte
                  (.hole "op:instanceOf")
                  (.ret (.field (.name "Object") "class"))
                  (.ifte
                    (.hole "op:instanceOf")
                    (.seq
                      .skip
                      (.seq
                        (.assign "bounds" (.call "getUpperBounds" []))
                        (.seq
                          (.expr
                            (.call "assert" [(.binop "==" (.hole "op:sizeOf") (.lit (.int 1)))]))
                          (.ret
                            (.call
                              "com.google.gson.internal.GsonTypes.getRawType:java.lang.Class(java.lang.reflect.Type)"
                              [(.index (.name "bounds") (.lit (.int 0)))])))))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "className"
                          (.cond
                            (.binop "==" (.name "type") (.lit .unit))
                            (.lit (.str "null"))
                            (.call "getName" [])))
                        (.hole "control:THROW")))))))) }

/-- `com.google.gson.internal.GsonTypes.equal:boolean(java.lang.Object,java.lang.Object)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_equal_boolean_java_lang_Object_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.GsonTypes.equal:boolean(java.lang.Object,java.lang.Object)"
  , params := ["a", "b"]
  , body := (.ret (.call "equals" [(.name "a"), (.name "b")])) }

/-- `com.google.gson.internal.GsonTypes.equals:boolean(java.lang.reflect.Type,java.lang.reflect.Type)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_equals_boolean_java_lang_reflect_Type_java_lang_reflect_Type_ : Func :=
  { name := "com.google.gson.internal.GsonTypes.equals:boolean(java.lang.reflect.Type,java.lang.reflect.Type)"
  , params := ["a", "b"]
  , body := (.seq
            .skip
            (.seq
              (.assign "areSame" (.binop "==" (.name "a") (.name "b")))
              (.ifte
                (.name "areSame")
                (.ret (.lit (.bool true)))
                (.ifte
                  (.hole "op:instanceOf")
                  (.ret (.call "equals" [(.name "b")]))
                  (.ifte
                    (.hole "op:instanceOf")
                    (.seq
                      (.ifte (.unop "!" (.hole "op:instanceOf")) (.ret (.lit (.bool false))) .skip)
                      (.seq
                        .skip
                        (.seq
                          (.assign "pa" (.hole "op:cast"))
                          (.seq
                            .skip
                            (.seq
                              (.assign "pb" (.hole "op:cast"))
                              (.ret
                                (.binop
                                  "&&"
                                  (.binop
                                    "&&"
                                    (.call
                                      "com.google.gson.internal.GsonTypes.equal:boolean(java.lang.Object,java.lang.Object)"
                                      [(.call "getOwnerType" []), (.call "getOwnerType" [])])
                                    (.call "equals" [(.call "getRawType" [])]))
                                  (.call
                                    "equals"
                                    [ (.call "getActualTypeArguments" [])
                                    , (.call "getActualTypeArguments" []) ]))))))))
                    (.ifte
                      (.hole "op:instanceOf")
                      (.seq
                        (.ifte
                          (.unop "!" (.hole "op:instanceOf"))
                          (.ret (.lit (.bool false)))
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.assign "ga" (.hole "op:cast"))
                            (.seq
                              .skip
                              (.seq
                                (.assign "gb" (.hole "op:cast"))
                                (.ret
                                  (.call
                                    "com.google.gson.internal.GsonTypes.equals:boolean(java.lang.reflect.Type,java.lang.reflect.Type)"
                                    [ (.call "getGenericComponentType" [])
                                    , (.call "getGenericComponentType" []) ])))))))
                      (.ifte
                        (.hole "op:instanceOf")
                        (.seq
                          (.ifte
                            (.unop "!" (.hole "op:instanceOf"))
                            (.ret (.lit (.bool false)))
                            .skip)
                          (.seq
                            .skip
                            (.seq
                              (.assign "wa" (.hole "op:cast"))
                              (.seq
                                .skip
                                (.seq
                                  (.assign "wb" (.hole "op:cast"))
                                  (.ret
                                    (.binop
                                      "&&"
                                      (.call
                                        "equals"
                                        [(.call "getUpperBounds" []), (.call "getUpperBounds" [])])
                                      (.call
                                        "equals"
                                        [(.call "getLowerBounds" []), (.call "getLowerBounds" [])]))))))))
                        (.ifte
                          (.hole "op:instanceOf")
                          (.seq
                            (.ifte
                              (.unop "!" (.hole "op:instanceOf"))
                              (.ret (.lit (.bool false)))
                              .skip)
                            (.seq
                              .skip
                              (.seq
                                (.assign "va" (.hole "op:cast"))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "vb" (.hole "op:cast"))
                                    (.ret
                                      (.binop
                                        "&&"
                                        (.call
                                        "equals"
                                        [ (.call "getGenericDeclaration" [])
                                        , (.call "getGenericDeclaration" []) ])
                                        (.call "equals" [(.call "getName" [])]))))))))
                          (.ret (.lit (.bool false))))))))))) }

/-- `com.google.gson.internal.GsonTypes.typeToString:java.lang.String(java.lang.reflect.Type)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_typeToString_java_lang_String_java_lang_reflect_Type_ : Func :=
  { name := "com.google.gson.internal.GsonTypes.typeToString:java.lang.String(java.lang.reflect.Type)"
  , params := ["type"]
  , body := (.ret (.cond (.hole "op:instanceOf") (.call "getName" []) (.call "toString" []))) }

/-- `com.google.gson.internal.GsonTypes.getGenericSupertype:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.Class)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_getGenericSupertype_java_lang_reflect_Type_java_lang_reflect_Type_java_lang_Class_j : Func :=
  { name := "com.google.gson.internal.GsonTypes.getGenericSupertype:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.Class)"
  , params := ["context", "rawType", "supertype"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "supertype") (.name "rawType"))
              (.ret (.name "context"))
              .skip)
            (.seq
              (.ifte
                (.call "isInterface" [])
                (.seq
                  .skip
                  (.seq (.assign "interfaces" (.call "getInterfaces" [])) (.hole "control:FOR")))
                .skip)
              (.seq
                (.ifte
                  (.unop "!" (.call "isInterface" []))
                  (.loop
                    (.binop "!=" (.name "rawType") (.field (.name "Object") "class"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "rawSupertype" (.call "getSuperclass" []))
                        (.seq
                          (.ifte
                            (.binop "==" (.name "rawSupertype") (.name "supertype"))
                            (.ret (.call "getGenericSuperclass" []))
                            (.ifte
                              (.call "isAssignableFrom" [(.name "rawSupertype")])
                              (.ret
                                (.call
                                  "com.google.gson.internal.GsonTypes.getGenericSupertype:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.Class)"
                                  [ (.call "getGenericSuperclass" [])
                                  , (.name "rawSupertype")
                                  , (.name "supertype") ]))
                              .skip))
                          (.assign "rawType" (.name "rawSupertype"))))))
                  .skip)
                (.ret (.name "supertype"))))) }

/-- `com.google.gson.internal.GsonTypes.getSupertype:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.Class)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_getSupertype_java_lang_reflect_Type_java_lang_reflect_Type_java_lang_Class_java_lan : Func :=
  { name := "com.google.gson.internal.GsonTypes.getSupertype:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.Class)"
  , params := ["context", "contextRawType", "supertype"]
  , body := (.seq
            (.ifte
              (.hole "op:instanceOf")
              (.seq
                .skip
                (.seq
                  (.assign "bounds" (.call "getUpperBounds" []))
                  (.seq
                    (.expr (.call "assert" [(.binop "==" (.hole "op:sizeOf") (.lit (.int 1)))]))
                    (.assign "context" (.index (.name "bounds") (.lit (.int 0)))))))
              .skip)
            (.seq
              (.ifte
                (.unop "!" (.call "isAssignableFrom" [(.name "contextRawType")]))
                (.hole "control:THROW")
                .skip)
              (.ret
                (.call
                  "com.google.gson.internal.GsonTypes.resolve:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type)"
                  [ (.name "context")
                  , (.name "contextRawType")
                  , (.call
                      "com.google.gson.internal.GsonTypes.getGenericSupertype:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.Class)"
                      [(.name "context"), (.name "contextRawType"), (.name "supertype")]) ])))) }

/-- `com.google.gson.internal.GsonTypes.getArrayComponentType:java.lang.reflect.Type(java.lang.reflect.Type)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_getArrayComponentType_java_lang_reflect_Type_java_lang_reflect_Type_ : Func :=
  { name := "com.google.gson.internal.GsonTypes.getArrayComponentType:java.lang.reflect.Type(java.lang.reflect.Type)"
  , params := ["array"]
  , body := (.ret
            (.cond
              (.hole "op:instanceOf")
              (.call "getGenericComponentType" [])
              (.call "getComponentType" []))) }

/-- `com.google.gson.internal.GsonTypes.getCollectionElementType:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_getCollectionElementType_java_lang_reflect_Type_java_lang_reflect_Type_java_lang_Cl : Func :=
  { name := "com.google.gson.internal.GsonTypes.getCollectionElementType:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class)"
  , params := ["context", "contextRawType"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "collectionType"
                (.call
                  "com.google.gson.internal.GsonTypes.getSupertype:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.Class)"
                  [ (.name "context")
                  , (.name "contextRawType")
                  , (.field (.name "Collection") "class") ]))
              (.seq
                (.ifte
                  (.hole "op:instanceOf")
                  (.ret (.index (.call "getActualTypeArguments" []) (.lit (.int 0))))
                  .skip)
                (.ret (.field (.name "Object") "class"))))) }

/-- `com.google.gson.internal.GsonTypes.getMapKeyAndValueTypes:java.lang.reflect.Type[](java.lang.reflect.Type,java.lang.Class)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_getMapKeyAndValueTypes_java_lang_reflect_Type___java_lang_reflect_Type_java_lang_Cl : Func :=
  { name := "com.google.gson.internal.GsonTypes.getMapKeyAndValueTypes:java.lang.reflect.Type[](java.lang.reflect.Type,java.lang.Class)"
  , params := ["context", "contextRawType"]
  , body := (.seq
            (.ifte
              (.mcall (.name "Properties") "class" [(.name "contextRawType")])
              (.ret (.hole "op:arrayInitializer"))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign
                  "mapType"
                  (.call
                    "com.google.gson.internal.GsonTypes.getSupertype:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.Class)"
                    [(.name "context"), (.name "contextRawType"), (.field (.name "Map") "class")]))
                (.seq
                  (.ifte
                    (.hole "op:instanceOf")
                    (.seq
                      .skip
                      (.seq
                        (.assign "mapParameterizedType" (.hole "op:cast"))
                        (.ret (.call "getActualTypeArguments" []))))
                    .skip)
                  (.ret (.hole "op:arrayInitializer")))))) }

/-- `com.google.gson.internal.GsonTypes.resolve:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_resolve_java_lang_reflect_Type_java_lang_reflect_Type_java_lang_Class_java_lang_ref : Func :=
  { name := "com.google.gson.internal.GsonTypes.resolve:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type)"
  , params := ["context", "contextRawType", "toResolve"]
  , body := (.ret
            (.call
              "com.google.gson.internal.GsonTypes.resolve:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type,java.util.Map)"
              [ (.name "context")
              , (.name "contextRawType")
              , (.name "toResolve")
              , (.hole "expr:BLOCK-impure") ])) }

/-- `com.google.gson.internal.GsonTypes.resolve:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type,java.util.Map)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_resolve_java_lang_reflect_Type_java_lang_reflect_Type_java_lang_Class_java_lang_ref' : Func :=
  { name := "com.google.gson.internal.GsonTypes.resolve:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type,java.util.Map)"
  , params := ["context", "contextRawType", "toResolve", "visitedTypeVariables"]
  , body := (.seq
            .skip
            (.seq
              (.assign "resolving" (.lit .unit))
              (.seq
                (.loop
                  (.lit (.bool true))
                  (.ifte
                    (.hole "op:instanceOf")
                    (.seq
                      .skip
                      (.seq
                        (.assign "typeVariable" (.hole "op:cast"))
                        (.seq
                          .skip
                          (.seq
                            (.assign "previouslyResolved" (.call "get" [(.name "typeVariable")]))
                            (.seq
                              (.ifte
                                (.binop "!=" (.name "previouslyResolved") (.lit .unit))
                                (.ret
                                  (.cond
                                    (.binop
                                      "=="
                                      (.name "previouslyResolved")
                                      (.field (.name "Void") "TYPE"))
                                    (.name "toResolve")
                                    (.name "previouslyResolved")))
                                .skip)
                              (.seq
                                (.expr
                                  (.call
                                    "put"
                                    [(.name "typeVariable"), (.field (.name "Void") "TYPE")]))
                                (.seq
                                  (.ifte
                                    (.binop "==" (.name "resolving") (.lit .unit))
                                    (.assign "resolving" (.name "typeVariable"))
                                    .skip)
                                  (.seq
                                    (.assign
                                      "toResolve"
                                      (.call
                                        "com.google.gson.internal.GsonTypes.resolveTypeVariable:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.TypeVariable)"
                                        [ (.name "context")
                                        , (.name "contextRawType")
                                        , (.name "typeVariable") ]))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "areSame"
                                        (.binop "==" (.name "toResolve") (.name "typeVariable")))
                                        (.ifte (.name "areSame") .brk .skip)))))))))))
                    (.ifte
                      (.binop "&&" (.hole "op:instanceOf") (.call "isArray" []))
                      (.seq
                        .skip
                        (.seq
                          (.assign "original" (.hole "op:cast"))
                          (.seq
                            .skip
                            (.seq
                              (.assign "componentType" (.call "getComponentType" []))
                              (.seq
                                .skip
                                (.seq
                                  (.assign
                                    "newComponentType"
                                    (.call
                                      "com.google.gson.internal.GsonTypes.resolve:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type,java.util.Map)"
                                      [ (.name "context")
                                      , (.name "contextRawType")
                                      , (.name "componentType")
                                      , (.name "visitedTypeVariables") ]))
                                  (.seq
                                    (.assign
                                      "toResolve"
                                      (.cond
                                        (.call
                                        "com.google.gson.internal.GsonTypes.equal:boolean(java.lang.Object,java.lang.Object)"
                                        [(.name "componentType"), (.name "newComponentType")])
                                        (.name "original")
                                        (.call
                                        "com.google.gson.internal.GsonTypes.arrayOf:java.lang.reflect.GenericArrayType(java.lang.reflect.Type)"
                                        [(.name "newComponentType")])))
                                    .brk)))))))
                      (.ifte
                        (.hole "op:instanceOf")
                        (.seq
                          .skip
                          (.seq
                            (.assign "original" (.hole "op:cast"))
                            (.seq
                              .skip
                              (.seq
                                (.assign "componentType" (.call "getGenericComponentType" []))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign
                                      "newComponentType"
                                      (.call
                                        "com.google.gson.internal.GsonTypes.resolve:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type,java.util.Map)"
                                        [ (.name "context")
                                        , (.name "contextRawType")
                                        , (.name "componentType")
                                        , (.name "visitedTypeVariables") ]))
                                    (.seq
                                      (.assign
                                        "toResolve"
                                        (.cond
                                        (.call
                                        "com.google.gson.internal.GsonTypes.equal:boolean(java.lang.Object,java.lang.Object)"
                                        [(.name "componentType"), (.name "newComponentType")])
                                        (.name "original")
                                        (.call
                                        "com.google.gson.internal.GsonTypes.arrayOf:java.lang.reflect.GenericArrayType(java.lang.reflect.Type)"
                                        [(.name "newComponentType")])))
                                      .brk)))))))
                        (.ifte
                          (.hole "op:instanceOf")
                          (.seq
                            .skip
                            (.seq
                              (.assign "original" (.hole "op:cast"))
                              (.seq
                                .skip
                                (.seq
                                  (.assign "ownerType" (.call "getOwnerType" []))
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign
                                        "newOwnerType"
                                        (.call
                                        "com.google.gson.internal.GsonTypes.resolve:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type,java.util.Map)"
                                        [ (.name "context")
                                        , (.name "contextRawType")
                                        , (.name "ownerType")
                                        , (.name "visitedTypeVariables") ]))
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "ownerChanged"
                                        (.unop
                                        "!"
                                        (.call
                                        "com.google.gson.internal.GsonTypes.equal:boolean(java.lang.Object,java.lang.Object)"
                                        [(.name "newOwnerType"), (.name "ownerType")])))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "args" (.call "getActualTypeArguments" []))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "argsChanged" (.lit (.bool false)))
                                        (.seq
                                        (.hole "control:FOR")
                                        (.seq
                                        (.assign
                                        "toResolve"
                                        (.cond
                                        (.binop "||" (.name "ownerChanged") (.name "argsChanged"))
                                        (.call
                                        "com.google.gson.internal.GsonTypes.newParameterizedTypeWithOwner:java.lang.reflect.ParameterizedType(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type[])"
                                        [ (.name "newOwnerType")
                                        , (.hole "op:cast")
                                        , (.hole "op:arrayInitializer") ])
                                        (.name "original")))
                                        .brk))))))))))))))
                          (.ifte
                            (.hole "op:instanceOf")
                            (.seq
                              .skip
                              (.seq
                                (.assign "original" (.hole "op:cast"))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "originalLowerBound" (.call "getLowerBounds" []))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign "originalUpperBound" (.call "getUpperBounds" []))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.hole "op:sizeOf") (.lit (.int 1)))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "lowerBound"
                                        (.call
                                        "com.google.gson.internal.GsonTypes.resolve:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type,java.util.Map)"
                                        [ (.name "context")
                                        , (.name "contextRawType")
                                        , (.index (.name "originalLowerBound") (.lit (.int 0)))
                                        , (.name "visitedTypeVariables") ]))
                                        (.ifte
                                        (.unop
                                        "!"
                                        (.call
                                        "com.google.gson.internal.GsonTypes.equal:boolean(java.lang.Object,java.lang.Object)"
                                        [ (.name "lowerBound")
                                        , (.index (.name "originalLowerBound") (.lit (.int 0))) ]))
                                        (.seq
                                        (.assign
                                        "toResolve"
                                        (.call
                                        "com.google.gson.internal.GsonTypes.supertypeOf:java.lang.reflect.WildcardType(java.lang.reflect.Type)"
                                        [(.name "lowerBound")]))
                                        .brk)
                                        .skip)))
                                        (.ifte
                                        (.binop "==" (.hole "op:sizeOf") (.lit (.int 1)))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "upperBound"
                                        (.call
                                        "com.google.gson.internal.GsonTypes.resolve:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type,java.util.Map)"
                                        [ (.name "context")
                                        , (.name "contextRawType")
                                        , (.index (.name "originalUpperBound") (.lit (.int 0)))
                                        , (.name "visitedTypeVariables") ]))
                                        (.ifte
                                        (.unop
                                        "!"
                                        (.call
                                        "com.google.gson.internal.GsonTypes.equal:boolean(java.lang.Object,java.lang.Object)"
                                        [ (.name "upperBound")
                                        , (.index (.name "originalUpperBound") (.lit (.int 0))) ]))
                                        (.seq
                                        (.assign
                                        "toResolve"
                                        (.call
                                        "com.google.gson.internal.GsonTypes.subtypeOf:java.lang.reflect.WildcardType(java.lang.reflect.Type)"
                                        [(.name "upperBound")]))
                                        .brk)
                                        .skip)))
                                        .skip))
                                        (.seq (.assign "toResolve" (.name "original")) .brk))))))))
                            .brk))))))
                (.seq
                  (.ifte
                    (.binop "!=" (.name "resolving") (.lit .unit))
                    (.expr (.call "put" [(.name "resolving"), (.name "toResolve")]))
                    .skip)
                  (.ret (.name "toResolve")))))) }

/-- `com.google.gson.internal.GsonTypes.resolveTypeVariable:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.TypeVariable)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_resolveTypeVariable_java_lang_reflect_Type_java_lang_reflect_Type_java_lang_Class_j : Func :=
  { name := "com.google.gson.internal.GsonTypes.resolveTypeVariable:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.TypeVariable)"
  , params := ["context", "contextRawType", "unknown"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "declaredByRaw"
                (.call
                  "com.google.gson.internal.GsonTypes.declaringClassOf:java.lang.Class(java.lang.reflect.TypeVariable)"
                  [(.name "unknown")]))
              (.seq
                (.ifte
                  (.binop "==" (.name "declaredByRaw") (.lit .unit))
                  (.ret (.name "unknown"))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "declaredBy"
                      (.call
                        "com.google.gson.internal.GsonTypes.getGenericSupertype:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.Class)"
                        [(.name "context"), (.name "contextRawType"), (.name "declaredByRaw")]))
                    (.seq
                      (.ifte
                        (.hole "op:instanceOf")
                        (.seq
                          .skip
                          (.seq
                            (.assign
                              "index"
                              (.call
                                "com.google.gson.internal.GsonTypes.indexOf:int(java.lang.Object[],java.lang.Object)"
                                [(.call "getTypeParameters" []), (.name "unknown")]))
                            (.ret (.index (.call "getActualTypeArguments" []) (.name "index")))))
                        .skip)
                      (.ret (.name "unknown")))))))) }

/-- `com.google.gson.internal.GsonTypes.indexOf:int(java.lang.Object[],java.lang.Object)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_indexOf_int_java_lang_Object___java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.GsonTypes.indexOf:int(java.lang.Object[],java.lang.Object)"
  , params := ["array", "toFind"]
  , body := (.seq (.hole "control:FOR") (.hole "control:THROW")) }

/-- `com.google.gson.internal.GsonTypes.declaringClassOf:java.lang.Class(java.lang.reflect.TypeVariable)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_declaringClassOf_java_lang_Class_java_lang_reflect_TypeVariable_ : Func :=
  { name := "com.google.gson.internal.GsonTypes.declaringClassOf:java.lang.Class(java.lang.reflect.TypeVariable)"
  , params := ["typeVariable"]
  , body := (.seq
            .skip
            (.seq
              (.assign "genericDeclaration" (.call "getGenericDeclaration" []))
              (.ret (.cond (.hole "op:instanceOf") (.hole "op:cast") (.lit .unit))))) }

/-- `com.google.gson.internal.GsonTypes.checkNotPrimitive:void(java.lang.reflect.Type)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_checkNotPrimitive_void_java_lang_reflect_Type_ : Func :=
  { name := "com.google.gson.internal.GsonTypes.checkNotPrimitive:void(java.lang.reflect.Type)"
  , params := ["type"]
  , body := (.ifte
            (.binop "&&" (.hole "op:instanceOf") (.call "isPrimitive" []))
            (.hole "control:THROW")
            .skip) }

/-- `com.google.gson.internal.GsonTypes.requiresOwnerType:boolean(java.lang.reflect.Type)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_requiresOwnerType_boolean_java_lang_reflect_Type_ : Func :=
  { name := "com.google.gson.internal.GsonTypes.requiresOwnerType:boolean(java.lang.reflect.Type)"
  , params := ["rawType"]
  , body := (.seq
            (.ifte
              (.hole "op:instanceOf")
              (.seq
                .skip
                (.seq
                  (.assign "rawTypeAsClass" (.hole "op:cast"))
                  (.ret
                    (.binop
                      "&&"
                      (.unop "!" (.call "isStatic" [(.call "getModifiers" [])]))
                      (.binop "!=" (.call "getDeclaringClass" []) (.lit .unit))))))
              .skip)
            (.ret (.lit (.bool false)))) }

/-- `com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.<init>:void(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type[])`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl__init__void_java_lang_reflect_Type_java_lang_Class_java_lang_ : Func :=
  { name := "com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.<init>:void(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type[])"
  , params := ["this", "ownerType", "rawType", "typeArguments"]
  , body := (.seq
            (.expr (.call "requireNonNull" [(.name "rawType")]))
            (.seq
              (.ifte
                (.binop
                  "&&"
                  (.binop "==" (.name "ownerType") (.lit .unit))
                  (.call
                    "com.google.gson.internal.GsonTypes.requiresOwnerType:boolean(java.lang.reflect.Type)"
                    [(.name "rawType")]))
                (.hole "control:THROW")
                .skip)
              (.seq
                (.setField
                  (.name "this")
                  "ownerType"
                  (.cond
                    (.binop "==" (.name "ownerType") (.lit .unit))
                    (.lit .unit)
                    (.call
                      "com.google.gson.internal.GsonTypes.canonicalize:java.lang.reflect.Type(java.lang.reflect.Type)"
                      [(.name "ownerType")])))
                (.seq
                  (.setField
                    (.name "this")
                    "rawType"
                    (.call
                      "com.google.gson.internal.GsonTypes.canonicalize:java.lang.reflect.Type(java.lang.reflect.Type)"
                      [(.name "rawType")]))
                  (.seq
                    (.setField (.name "this") "typeArguments" (.call "clone" []))
                    (.hole "control:FOR")))))) }

/-- `com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.getActualTypeArguments:java.lang.reflect.Type[]()`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_getActualTypeArguments_java_lang_reflect_Type____ : Func :=
  { name := "com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.getActualTypeArguments:java.lang.reflect.Type[]()"
  , params := ["this"]
  , body := (.ret (.mcall (.name "this") "typeArguments" [])) }

/-- `com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.getRawType:java.lang.reflect.Type()`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_getRawType_java_lang_reflect_Type__ : Func :=
  { name := "com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.getRawType:java.lang.reflect.Type()"
  , params := ["this"]
  , body := (.ret (.field (.name "this") "rawType")) }

/-- `com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.getOwnerType:java.lang.reflect.Type()`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_getOwnerType_java_lang_reflect_Type__ : Func :=
  { name := "com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.getOwnerType:java.lang.reflect.Type()"
  , params := ["this"]
  , body := (.ret (.field (.name "this") "ownerType")) }

/-- `com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.equals:boolean(java.lang.Object)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_equals_boolean_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.equals:boolean(java.lang.Object)"
  , params := ["this", "other"]
  , body := (.ret
            (.binop
              "&&"
              (.hole "op:instanceOf")
              (.call
                "com.google.gson.internal.GsonTypes.equals:boolean(java.lang.reflect.Type,java.lang.reflect.Type)"
                [(.name "this"), (.hole "op:cast")]))) }

/-- `com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.hashCodeOrZero:int(java.lang.Object)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_hashCodeOrZero_int_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.hashCodeOrZero:int(java.lang.Object)"
  , params := ["o"]
  , body := (.ret
            (.cond (.binop "!=" (.name "o") (.lit .unit)) (.call "hashCode" []) (.lit (.int 0)))) }

/-- `com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.hashCode:int()`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_hashCode_int__ : Func :=
  { name := "com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.hashCode:int()"
  , params := ["this"]
  , body := (.ret (.hole "op:xor")) }

/-- `com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.toString:java.lang.String()`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_toString_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.GsonTypes$ParameterizedTypeImpl.toString:java.lang.String()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "length" (.hole "op:sizeOf"))
              (.seq
                (.ifte
                  (.binop "==" (.name "length") (.lit (.int 0)))
                  (.ret (.mcall (.name "this") "rawType" [(.field (.name "this") "rawType")]))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "stringBuilder" (.hole "op:alloc"))
                    (.seq
                      (.expr
                        (.call
                          "<init>"
                          [ (.binop
                              "*"
                              (.lit (.int 30))
                              (.binop "+" (.name "length") (.lit (.int 1)))) ]))
                      (.seq
                        (.expr
                          (.call
                            "append"
                            [ (.call
                                "com.google.gson.internal.GsonTypes.typeToString:java.lang.String(java.lang.reflect.Type)"
                                [(.index (.field (.name "this") "typeArguments") (.lit (.int 0)))]) ]))
                        (.seq (.hole "control:FOR") (.ret (.call "toString" [])))))))))) }

/-- `com.google.gson.internal.GsonTypes$GenericArrayTypeImpl.<init>:void(java.lang.reflect.Type)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_GenericArrayTypeImpl__init__void_java_lang_reflect_Type_ : Func :=
  { name := "com.google.gson.internal.GsonTypes$GenericArrayTypeImpl.<init>:void(java.lang.reflect.Type)"
  , params := ["this", "componentType"]
  , body := (.seq
            (.expr (.call "requireNonNull" [(.name "componentType")]))
            (.setField
              (.name "this")
              "componentType"
              (.call
                "com.google.gson.internal.GsonTypes.canonicalize:java.lang.reflect.Type(java.lang.reflect.Type)"
                [(.name "componentType")]))) }

/-- `com.google.gson.internal.GsonTypes$GenericArrayTypeImpl.getGenericComponentType:java.lang.reflect.Type()`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_GenericArrayTypeImpl_getGenericComponentType_java_lang_reflect_Type__ : Func :=
  { name := "com.google.gson.internal.GsonTypes$GenericArrayTypeImpl.getGenericComponentType:java.lang.reflect.Type()"
  , params := ["this"]
  , body := (.ret (.field (.name "this") "componentType")) }

/-- `com.google.gson.internal.GsonTypes$GenericArrayTypeImpl.equals:boolean(java.lang.Object)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_GenericArrayTypeImpl_equals_boolean_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.GsonTypes$GenericArrayTypeImpl.equals:boolean(java.lang.Object)"
  , params := ["this", "o"]
  , body := (.ret
            (.binop
              "&&"
              (.hole "op:instanceOf")
              (.call
                "com.google.gson.internal.GsonTypes.equals:boolean(java.lang.reflect.Type,java.lang.reflect.Type)"
                [(.name "this"), (.hole "op:cast")]))) }

/-- `com.google.gson.internal.GsonTypes$GenericArrayTypeImpl.hashCode:int()`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_GenericArrayTypeImpl_hashCode_int__ : Func :=
  { name := "com.google.gson.internal.GsonTypes$GenericArrayTypeImpl.hashCode:int()"
  , params := ["this"]
  , body := (.ret (.mcall (.name "this") "componentType" [])) }

/-- `com.google.gson.internal.GsonTypes$GenericArrayTypeImpl.toString:java.lang.String()`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_GenericArrayTypeImpl_toString_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.GsonTypes$GenericArrayTypeImpl.toString:java.lang.String()"
  , params := ["this"]
  , body := (.ret
            (.binop
              "+"
              (.mcall (.name "this") "componentType" [(.field (.name "this") "componentType")])
              (.lit (.str "[]")))) }

/-- `com.google.gson.internal.GsonTypes$WildcardTypeImpl.<init>:void(java.lang.reflect.Type[],java.lang.reflect.Type[])`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_WildcardTypeImpl__init__void_java_lang_reflect_Type___java_lang_reflect_Type___ : Func :=
  { name := "com.google.gson.internal.GsonTypes$WildcardTypeImpl.<init>:void(java.lang.reflect.Type[],java.lang.reflect.Type[])"
  , params := ["this", "upperBounds", "lowerBounds"]
  , body := (.seq
            (.ifte (.binop ">" (.hole "op:sizeOf") (.lit (.int 1))) (.hole "control:THROW") .skip)
            (.seq
              (.ifte
                (.binop "!=" (.hole "op:sizeOf") (.lit (.int 1)))
                (.hole "control:THROW")
                .skip)
              (.ifte
                (.binop "==" (.hole "op:sizeOf") (.lit (.int 1)))
                (.seq
                  (.expr (.call "requireNonNull" [(.index (.name "lowerBounds") (.lit (.int 0)))]))
                  (.seq
                    (.expr
                      (.call
                        "com.google.gson.internal.GsonTypes.checkNotPrimitive:void(java.lang.reflect.Type)"
                        [(.index (.name "lowerBounds") (.lit (.int 0)))]))
                    (.seq
                      (.ifte
                        (.binop
                          "!="
                          (.index (.name "upperBounds") (.lit (.int 0)))
                          (.field (.name "Object") "class"))
                        (.hole "control:THROW")
                        .skip)
                      (.seq
                        (.setField
                          (.name "this")
                          "lowerBound"
                          (.call
                            "com.google.gson.internal.GsonTypes.canonicalize:java.lang.reflect.Type(java.lang.reflect.Type)"
                            [(.index (.name "lowerBounds") (.lit (.int 0)))]))
                        (.setField (.name "this") "upperBound" (.field (.name "Object") "class"))))))
                (.seq
                  (.expr (.call "requireNonNull" [(.index (.name "upperBounds") (.lit (.int 0)))]))
                  (.seq
                    (.expr
                      (.call
                        "com.google.gson.internal.GsonTypes.checkNotPrimitive:void(java.lang.reflect.Type)"
                        [(.index (.name "upperBounds") (.lit (.int 0)))]))
                    (.seq
                      (.setField (.name "this") "lowerBound" (.lit .unit))
                      (.setField
                        (.name "this")
                        "upperBound"
                        (.call
                          "com.google.gson.internal.GsonTypes.canonicalize:java.lang.reflect.Type(java.lang.reflect.Type)"
                          [(.index (.name "upperBounds") (.lit (.int 0)))])))))))) }

/-- `com.google.gson.internal.GsonTypes$WildcardTypeImpl.getUpperBounds:java.lang.reflect.Type[]()`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_WildcardTypeImpl_getUpperBounds_java_lang_reflect_Type____ : Func :=
  { name := "com.google.gson.internal.GsonTypes$WildcardTypeImpl.getUpperBounds:java.lang.reflect.Type[]()"
  , params := ["this"]
  , body := (.ret (.hole "op:arrayInitializer")) }

/-- `com.google.gson.internal.GsonTypes$WildcardTypeImpl.getLowerBounds:java.lang.reflect.Type[]()`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_WildcardTypeImpl_getLowerBounds_java_lang_reflect_Type____ : Func :=
  { name := "com.google.gson.internal.GsonTypes$WildcardTypeImpl.getLowerBounds:java.lang.reflect.Type[]()"
  , params := ["this"]
  , body := (.ret
            (.cond
              (.binop "!=" (.field (.name "this") "lowerBound") (.lit .unit))
              (.hole "op:arrayInitializer")
              (.field (.fnref "com.google.gson.internal.GsonTypes") "EMPTY_TYPE_ARRAY"))) }

/-- `com.google.gson.internal.GsonTypes$WildcardTypeImpl.equals:boolean(java.lang.Object)`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_WildcardTypeImpl_equals_boolean_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.GsonTypes$WildcardTypeImpl.equals:boolean(java.lang.Object)"
  , params := ["this", "other"]
  , body := (.ret
            (.binop
              "&&"
              (.hole "op:instanceOf")
              (.call
                "com.google.gson.internal.GsonTypes.equals:boolean(java.lang.reflect.Type,java.lang.reflect.Type)"
                [(.name "this"), (.hole "op:cast")]))) }

/-- `com.google.gson.internal.GsonTypes$WildcardTypeImpl.hashCode:int()`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_WildcardTypeImpl_hashCode_int__ : Func :=
  { name := "com.google.gson.internal.GsonTypes$WildcardTypeImpl.hashCode:int()"
  , params := ["this"]
  , body := (.ret (.hole "op:xor")) }

/-- `com.google.gson.internal.GsonTypes$WildcardTypeImpl.toString:java.lang.String()`  (from `internal/GsonTypes.java`) -/
def f_com_google_gson_internal_GsonTypes_WildcardTypeImpl_toString_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.GsonTypes$WildcardTypeImpl.toString:java.lang.String()"
  , params := ["this"]
  , body := (.ifte
            (.binop "!=" (.field (.name "this") "lowerBound") (.lit .unit))
            (.ret
              (.binop
                "+"
                (.lit (.str "? super "))
                (.mcall (.name "this") "lowerBound" [(.field (.name "this") "lowerBound")])))
            (.ifte
              (.binop "==" (.field (.name "this") "upperBound") (.field (.name "Object") "class"))
              (.ret (.lit (.str "?")))
              (.ret
                (.binop
                  "+"
                  (.lit (.str "? extends "))
                  (.mcall (.name "this") "upperBound" [(.field (.name "this") "upperBound")]))))) }

/-- `com.google.gson.internal.GsonTypes.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_GsonTypes__clinit__void__ : Func :=
  { name := "com.google.gson.internal.GsonTypes.<clinit>:void()"
  , params := []
  , body := (.setField
            (.fnref "com.google.gson.internal.GsonTypes")
            "EMPTY_TYPE_ARRAY"
            (.hole "op:arrayInitializer")) }

/-- `com.google.gson.internal.JavaVersion.determineMajorJavaVersion:int()`  (from `internal/JavaVersion.java`) -/
def f_com_google_gson_internal_JavaVersion_determineMajorJavaVersion_int__ : Func :=
  { name := "com.google.gson.internal.JavaVersion.determineMajorJavaVersion:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "javaVersion" (.call "getProperty" [(.lit (.str "java.version"))]))
              (.ret
                (.call
                  "com.google.gson.internal.JavaVersion.parseMajorJavaVersion:int(java.lang.String)"
                  [(.name "javaVersion")])))) }

/-- `com.google.gson.internal.JavaVersion.parseMajorJavaVersion:int(java.lang.String)`  (from `internal/JavaVersion.java`) -/
def f_com_google_gson_internal_JavaVersion_parseMajorJavaVersion_int_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.JavaVersion.parseMajorJavaVersion:int(java.lang.String)"
  , params := ["javaVersion"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "version"
                (.call
                  "com.google.gson.internal.JavaVersion.parseDotted:int(java.lang.String)"
                  [(.name "javaVersion")]))
              (.seq
                (.ifte
                  (.binop "==" (.name "version") (.unop "-" (.lit (.int 1))))
                  (.assign
                    "version"
                    (.call
                      "com.google.gson.internal.JavaVersion.extractBeginningInt:int(java.lang.String)"
                      [(.name "javaVersion")]))
                  .skip)
                (.seq
                  (.ifte
                    (.binop "==" (.name "version") (.unop "-" (.lit (.int 1))))
                    (.ret (.lit (.int 6)))
                    .skip)
                  (.ret (.name "version")))))) }

/-- `com.google.gson.internal.JavaVersion.parseDotted:int(java.lang.String)`  (from `internal/JavaVersion.java`) -/
def f_com_google_gson_internal_JavaVersion_parseDotted_int_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.JavaVersion.parseDotted:int(java.lang.String)"
  , params := ["javaVersion"]
  , body := (.tryCatch
            (.seq
              .skip
              (.seq
                (.assign "parts" (.call "split" [(.lit (.str "[._]")), (.lit (.int 3))]))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "firstVer"
                      (.call "parseInt" [(.index (.name "parts") (.lit (.int 0)))]))
                    (.ifte
                      (.binop
                        "&&"
                        (.binop "==" (.name "firstVer") (.lit (.int 1)))
                        (.binop ">" (.hole "op:sizeOf") (.lit (.int 1))))
                      (.ret (.call "parseInt" [(.index (.name "parts") (.lit (.int 1)))]))
                      (.ret (.name "firstVer")))))))
            "__exc"
            (.ret (.unop "-" (.lit (.int 1))))) }

/-- `com.google.gson.internal.JavaVersion.extractBeginningInt:int(java.lang.String)`  (from `internal/JavaVersion.java`) -/
def f_com_google_gson_internal_JavaVersion_extractBeginningInt_int_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.JavaVersion.extractBeginningInt:int(java.lang.String)"
  , params := ["javaVersion"]
  , body := (.tryCatch
            (.seq
              .skip
              (.seq
                (.assign "num" (.hole "op:alloc"))
                (.seq
                  (.expr (.call "<init>" []))
                  (.seq (.hole "control:FOR") (.ret (.call "parseInt" [(.call "toString" [])]))))))
            "__exc"
            (.ret (.unop "-" (.lit (.int 1))))) }

/-- `com.google.gson.internal.JavaVersion.getMajorJavaVersion:int()`  (from `internal/JavaVersion.java`) -/
def f_com_google_gson_internal_JavaVersion_getMajorJavaVersion_int__ : Func :=
  { name := "com.google.gson.internal.JavaVersion.getMajorJavaVersion:int()"
  , params := []
  , body := (.ret (.field (.fnref "com.google.gson.internal.JavaVersion") "majorJavaVersion")) }

/-- `com.google.gson.internal.JavaVersion.isJava9OrLater:boolean()`  (from `internal/JavaVersion.java`) -/
def f_com_google_gson_internal_JavaVersion_isJava9OrLater_boolean__ : Func :=
  { name := "com.google.gson.internal.JavaVersion.isJava9OrLater:boolean()"
  , params := []
  , body := (.ret
            (.binop
              ">="
              (.field (.fnref "com.google.gson.internal.JavaVersion") "majorJavaVersion")
              (.lit (.int 9)))) }

/-- `com.google.gson.internal.JavaVersion.<init>:void()`  (from `internal/JavaVersion.java`) -/
def f_com_google_gson_internal_JavaVersion__init__void__ : Func :=
  { name := "com.google.gson.internal.JavaVersion.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.JavaVersion.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_JavaVersion__clinit__void__ : Func :=
  { name := "com.google.gson.internal.JavaVersion.<clinit>:void()"
  , params := []
  , body := (.setField
            (.fnref "com.google.gson.internal.JavaVersion")
            "majorJavaVersion"
            (.call "com.google.gson.internal.JavaVersion.determineMajorJavaVersion:int()" [])) }

/-- `com.google.gson.internal.JsonReaderInternalAccess.promoteNameToValue:void(com.google.gson.stream.JsonReader)`  (from `internal/JsonReaderInternalAccess.java`) -/
def f_com_google_gson_internal_JsonReaderInternalAccess_promoteNameToValue_void_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.JsonReaderInternalAccess.promoteNameToValue:void(com.google.gson.stream.JsonReader)"
  , params := ["this", "reader"]
  , body := .skip }

/-- `com.google.gson.internal.JsonReaderInternalAccess.<init>:void()`  (from `internal/JsonReaderInternalAccess.java`) -/
def f_com_google_gson_internal_JsonReaderInternalAccess__init__void__ : Func :=
  { name := "com.google.gson.internal.JsonReaderInternalAccess.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.LazilyParsedNumber.<init>:void(java.lang.String)`  (from `internal/LazilyParsedNumber.java`) -/
def f_com_google_gson_internal_LazilyParsedNumber__init__void_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.LazilyParsedNumber.<init>:void(java.lang.String)"
  , params := ["this", "value"]
  , body := (.setField (.name "this") "value" (.name "value")) }

/-- `com.google.gson.internal.LazilyParsedNumber.asBigDecimal:java.math.BigDecimal()`  (from `internal/LazilyParsedNumber.java`) -/
def f_com_google_gson_internal_LazilyParsedNumber_asBigDecimal_java_math_BigDecimal__ : Func :=
  { name := "com.google.gson.internal.LazilyParsedNumber.asBigDecimal:java.math.BigDecimal()"
  , params := ["this"]
  , body := (.ret
            (.call
              "com.google.gson.internal.NumberLimits.parseBigDecimal:java.math.BigDecimal(java.lang.String)"
              [(.field (.name "this") "value")])) }

/-- `com.google.gson.internal.LazilyParsedNumber.intValue:int()`  (from `internal/LazilyParsedNumber.java`) -/
def f_com_google_gson_internal_LazilyParsedNumber_intValue_int__ : Func :=
  { name := "com.google.gson.internal.LazilyParsedNumber.intValue:int()"
  , params := ["this"]
  , body := (.tryCatch
            (.ret (.call "parseInt" [(.field (.name "this") "value")]))
            "__exc"
            (.tryCatch (.ret (.hole "op:cast")) "__exc" (.ret (.call "intValue" [])))) }

/-- `com.google.gson.internal.LazilyParsedNumber.longValue:long()`  (from `internal/LazilyParsedNumber.java`) -/
def f_com_google_gson_internal_LazilyParsedNumber_longValue_long__ : Func :=
  { name := "com.google.gson.internal.LazilyParsedNumber.longValue:long()"
  , params := ["this"]
  , body := (.tryCatch
            (.ret (.call "parseLong" [(.field (.name "this") "value")]))
            "__exc"
            (.ret (.call "longValue" []))) }

/-- `com.google.gson.internal.LazilyParsedNumber.floatValue:float()`  (from `internal/LazilyParsedNumber.java`) -/
def f_com_google_gson_internal_LazilyParsedNumber_floatValue_float__ : Func :=
  { name := "com.google.gson.internal.LazilyParsedNumber.floatValue:float()"
  , params := ["this"]
  , body := (.ret (.call "parseFloat" [(.field (.name "this") "value")])) }

/-- `com.google.gson.internal.LazilyParsedNumber.doubleValue:double()`  (from `internal/LazilyParsedNumber.java`) -/
def f_com_google_gson_internal_LazilyParsedNumber_doubleValue_double__ : Func :=
  { name := "com.google.gson.internal.LazilyParsedNumber.doubleValue:double()"
  , params := ["this"]
  , body := (.ret (.call "parseDouble" [(.field (.name "this") "value")])) }

/-- `com.google.gson.internal.LazilyParsedNumber.toString:java.lang.String()`  (from `internal/LazilyParsedNumber.java`) -/
def f_com_google_gson_internal_LazilyParsedNumber_toString_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.LazilyParsedNumber.toString:java.lang.String()"
  , params := ["this"]
  , body := (.ret (.field (.name "this") "value")) }

/-- `com.google.gson.internal.LazilyParsedNumber.writeReplace:java.lang.Object()`  (from `internal/LazilyParsedNumber.java`) -/
def f_com_google_gson_internal_LazilyParsedNumber_writeReplace_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.LazilyParsedNumber.writeReplace:java.lang.Object()"
  , params := ["this"]
  , body := (.ret
            (.call
              "com.google.gson.internal.LazilyParsedNumber.asBigDecimal:java.math.BigDecimal()"
              [])) }

/-- `com.google.gson.internal.LazilyParsedNumber.readObject:void(java.io.ObjectInputStream)`  (from `internal/LazilyParsedNumber.java`) -/
def f_com_google_gson_internal_LazilyParsedNumber_readObject_void_java_io_ObjectInputStream_ : Func :=
  { name := "com.google.gson.internal.LazilyParsedNumber.readObject:void(java.io.ObjectInputStream)"
  , params := ["this", "in"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.LazilyParsedNumber.compareTo:int(com.google.gson.internal.LazilyParsedNumber)`  (from `internal/LazilyParsedNumber.java`) -/
def f_com_google_gson_internal_LazilyParsedNumber_compareTo_int_com_google_gson_internal_LazilyParsedNumber_ : Func :=
  { name := "com.google.gson.internal.LazilyParsedNumber.compareTo:int(com.google.gson.internal.LazilyParsedNumber)"
  , params := ["this", "other"]
  , body := (.ret (.mcall (.name "this") "value" [(.field (.name "other") "value")])) }

/-- `com.google.gson.internal.LazilyParsedNumber.hashCode:int()`  (from `internal/LazilyParsedNumber.java`) -/
def f_com_google_gson_internal_LazilyParsedNumber_hashCode_int__ : Func :=
  { name := "com.google.gson.internal.LazilyParsedNumber.hashCode:int()"
  , params := ["this"]
  , body := (.ret (.mcall (.name "this") "value" [])) }

/-- `com.google.gson.internal.LazilyParsedNumber.equals:boolean(java.lang.Object)`  (from `internal/LazilyParsedNumber.java`) -/
def f_com_google_gson_internal_LazilyParsedNumber_equals_boolean_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.LazilyParsedNumber.equals:boolean(java.lang.Object)"
  , params := ["this", "obj"]
  , body := (.seq
            (.ifte (.binop "==" (.name "this") (.name "obj")) (.ret (.lit (.bool true))) .skip)
            (.seq
              (.ifte
                (.hole "op:instanceOf")
                (.seq
                  .skip
                  (.seq
                    (.assign "other" (.hole "op:cast"))
                    (.ret (.mcall (.name "this") "value" [(.field (.name "other") "value")]))))
                .skip)
              (.ret (.lit (.bool false))))) }

/-- `com.google.gson.internal.LinkedTreeMap.<init>:void()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap__init__void__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.<init>:void()"
  , params := ["this"]
  , body := (.expr
            (.call
              "com.google.gson.internal.LinkedTreeMap.<init>:void(java.util.Comparator,boolean)"
              [(.lit .unit), (.lit (.bool true))])) }

/-- `com.google.gson.internal.LinkedTreeMap.<init>:void(boolean)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap__init__void_boolean_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.<init>:void(boolean)"
  , params := ["this", "allowNullValues"]
  , body := (.expr
            (.call
              "com.google.gson.internal.LinkedTreeMap.<init>:void(java.util.Comparator,boolean)"
              [(.lit .unit), (.name "allowNullValues")])) }

/-- `com.google.gson.internal.LinkedTreeMap.<init>:void(java.util.Comparator,boolean)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap__init__void_java_util_Comparator_boolean_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.<init>:void(java.util.Comparator,boolean)"
  , params := ["this", "comparator", "allowNullValues"]
  , body := (.seq
            (.setField (.name "this") "size" (.lit (.int 0)))
            (.seq
              (.setField (.name "this") "modCount" (.lit (.int 0)))
              (.seq
                (.setField (.name "this") "comparator" (.name "comparator"))
                (.seq
                  (.setField (.name "this") "allowNullValues" (.name "allowNullValues"))
                  (.seq
                    (.setField (.name "this") "header" (.hole "op:alloc"))
                    (.expr
                      (.mcall (.name "this") "header" [(.name "allowNullValues"), (.name "this")]))))))) }

/-- `com.google.gson.internal.LinkedTreeMap.size:int()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_size_int__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.size:int()"
  , params := ["this"]
  , body := (.ret (.field (.name "this") "size")) }

/-- `com.google.gson.internal.LinkedTreeMap.get:java.lang.Object(java.lang.Object)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_get_java_lang_Object_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.get:java.lang.Object(java.lang.Object)"
  , params := ["this", "key"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "node"
                (.call
                  "com.google.gson.internal.LinkedTreeMap.findByObject:com.google.gson.internal.LinkedTreeMap$Node(java.lang.Object)"
                  [(.name "key")]))
              (.ret
                (.cond
                  (.binop "!=" (.name "node") (.lit .unit))
                  (.field (.name "node") "value")
                  (.lit .unit))))) }

/-- `com.google.gson.internal.LinkedTreeMap.containsKey:boolean(java.lang.Object)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_containsKey_boolean_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.containsKey:boolean(java.lang.Object)"
  , params := ["this", "key"]
  , body := (.ret
            (.binop
              "!="
              (.call
                "com.google.gson.internal.LinkedTreeMap.findByObject:com.google.gson.internal.LinkedTreeMap$Node(java.lang.Object)"
                [(.name "key")])
              (.lit .unit))) }

/-- `com.google.gson.internal.LinkedTreeMap.put:java.lang.Object(java.lang.Object,java.lang.Object)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_put_java_lang_Object_java_lang_Object_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.put:java.lang.Object(java.lang.Object,java.lang.Object)"
  , params := ["this", "key", "value"]
  , body := (.seq
            (.ifte (.binop "==" (.name "key") (.lit .unit)) (.hole "control:THROW") .skip)
            (.seq
              (.ifte
                (.binop
                  "&&"
                  (.binop "==" (.name "value") (.lit .unit))
                  (.unop "!" (.field (.name "this") "allowNullValues")))
                (.hole "control:THROW")
                .skip)
              (.seq
                .skip
                (.seq
                  (.assign
                    "created"
                    (.call
                      "com.google.gson.internal.LinkedTreeMap.find:com.google.gson.internal.LinkedTreeMap$Node(java.lang.Object,boolean)"
                      [(.name "key"), (.lit (.bool true))]))
                  (.seq
                    .skip
                    (.seq
                      (.assign "result" (.field (.name "created") "value"))
                      (.seq
                        (.setField (.name "created") "value" (.name "value"))
                        (.ret (.name "result"))))))))) }

/-- `com.google.gson.internal.LinkedTreeMap.clear:void()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_clear_void__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.clear:void()"
  , params := ["this"]
  , body := (.seq
            (.setField (.name "this") "root" (.lit .unit))
            (.seq
              (.setField (.name "this") "size" (.lit (.int 0)))
              (.seq
                (.expr (.hole "op:postIncrement"))
                (.seq
                  .skip
                  (.seq
                    (.assign "header" (.field (.name "this") "header"))
                    (.setField (.name "header") "next" (.hole "op:assignment"))))))) }

/-- `com.google.gson.internal.LinkedTreeMap.remove:java.lang.Object(java.lang.Object)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_remove_java_lang_Object_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.remove:java.lang.Object(java.lang.Object)"
  , params := ["this", "key"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "node"
                (.call
                  "com.google.gson.internal.LinkedTreeMap.removeInternalByKey:com.google.gson.internal.LinkedTreeMap$Node(java.lang.Object)"
                  [(.name "key")]))
              (.ret
                (.cond
                  (.binop "!=" (.name "node") (.lit .unit))
                  (.field (.name "node") "value")
                  (.lit .unit))))) }

/-- `com.google.gson.internal.LinkedTreeMap.find:com.google.gson.internal.LinkedTreeMap$Node(java.lang.Object,boolean)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_find_com_google_gson_internal_LinkedTreeMap_Node_java_lang_Object_boolean_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.find:com.google.gson.internal.LinkedTreeMap$Node(java.lang.Object,boolean)"
  , params := ["this", "key", "create"]
  , body := (.seq
            .skip
            (.seq
              (.assign "comparator" (.field (.name "this") "comparator"))
              (.seq
                .skip
                (.seq
                  (.assign "nearest" (.field (.name "this") "root"))
                  (.seq
                    .skip
                    (.seq
                      (.assign "comparison" (.lit (.int 0)))
                      (.seq
                        (.ifte
                          (.binop "!=" (.name "nearest") (.lit .unit))
                          (.seq
                            .skip
                            (.seq
                              (.assign
                                "comparableKey"
                                (.cond
                                  (.binop "==" (.name "comparator") (.lit .unit))
                                  (.hole "op:cast")
                                  (.lit .unit)))
                              (.loop
                                (.lit (.bool true))
                                (.seq
                                  (.assign
                                    "comparison"
                                    (.cond
                                      (.binop "!=" (.name "comparableKey") (.lit .unit))
                                      (.call "compareTo" [(.field (.name "nearest") "key")])
                                      (.call
                                        "compare"
                                        [(.name "key"), (.field (.name "nearest") "key")])))
                                  (.seq
                                    (.ifte
                                      (.binop "==" (.name "comparison") (.lit (.int 0)))
                                      (.ret (.name "nearest"))
                                      .skip)
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "child"
                                        (.cond
                                        (.binop "<" (.name "comparison") (.lit (.int 0)))
                                        (.field (.name "nearest") "left")
                                        (.field (.name "nearest") "right")))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "child") (.lit .unit))
                                        .brk
                                        .skip)
                                        (.assign "nearest" (.name "child"))))))))))
                          .skip)
                        (.seq
                          (.ifte (.unop "!" (.name "create")) (.ret (.lit .unit)) .skip)
                          (.seq
                            .skip
                            (.seq
                              (.assign "header" (.field (.name "this") "header"))
                              (.seq
                                .skip
                                (.seq
                                  (.ifte
                                    (.binop "==" (.name "nearest") (.lit .unit))
                                    (.seq
                                      (.ifte
                                        (.binop
                                        "&&"
                                        (.binop "==" (.name "comparator") (.lit .unit))
                                        (.unop "!" (.hole "op:instanceOf")))
                                        (.hole "control:THROW")
                                        .skip)
                                      (.seq
                                        (.assign "created" (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.LinkedTreeMap$Node.<init>:void(boolean,com.google.gson.internal.LinkedTreeMap$Node,java.lang.Object,com.google.gson.internal.LinkedTreeMap$Node,com.google.gson.internal.LinkedTreeMap$Node)"
                                        [ (.field (.name "this") "allowNullValues")
                                        , (.name "nearest")
                                        , (.name "key")
                                        , (.name "header")
                                        , (.field (.name "header") "prev") ]))
                                        (.setField (.name "this") "root" (.name "created")))))
                                    (.seq
                                      (.assign "created" (.hole "op:alloc"))
                                      (.seq
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.LinkedTreeMap$Node.<init>:void(boolean,com.google.gson.internal.LinkedTreeMap$Node,java.lang.Object,com.google.gson.internal.LinkedTreeMap$Node,com.google.gson.internal.LinkedTreeMap$Node)"
                                        [ (.field (.name "this") "allowNullValues")
                                        , (.name "nearest")
                                        , (.name "key")
                                        , (.name "header")
                                        , (.field (.name "header") "prev") ]))
                                        (.seq
                                        (.ifte
                                        (.binop "<" (.name "comparison") (.lit (.int 0)))
                                        (.setField (.name "nearest") "left" (.name "created"))
                                        (.setField (.name "nearest") "right" (.name "created")))
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.LinkedTreeMap.rebalance:void(com.google.gson.internal.LinkedTreeMap$Node,boolean)"
                                        [(.name "nearest"), (.lit (.bool true))]))))))
                                  (.seq
                                    (.expr (.hole "op:postIncrement"))
                                    (.seq
                                      (.expr (.hole "op:postIncrement"))
                                      (.ret (.name "created")))))))))))))))) }

/-- `com.google.gson.internal.LinkedTreeMap.findByObject:com.google.gson.internal.LinkedTreeMap$Node(java.lang.Object)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_findByObject_com_google_gson_internal_LinkedTreeMap_Node_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.findByObject:com.google.gson.internal.LinkedTreeMap$Node(java.lang.Object)"
  , params := ["this", "key"]
  , body := (.tryCatch
            (.ret
              (.cond
                (.binop "!=" (.name "key") (.lit .unit))
                (.call
                  "com.google.gson.internal.LinkedTreeMap.find:com.google.gson.internal.LinkedTreeMap$Node(java.lang.Object,boolean)"
                  [(.hole "op:cast"), (.lit (.bool false))])
                (.lit .unit)))
            "__exc"
            (.ret (.lit .unit))) }

/-- `com.google.gson.internal.LinkedTreeMap.findByEntry:com.google.gson.internal.LinkedTreeMap$Node(java.util.Map$Entry)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_findByEntry_com_google_gson_internal_LinkedTreeMap_Node_java_util_Map_Entry_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.findByEntry:com.google.gson.internal.LinkedTreeMap$Node(java.util.Map$Entry)"
  , params := ["this", "entry"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "mine"
                (.call
                  "com.google.gson.internal.LinkedTreeMap.findByObject:com.google.gson.internal.LinkedTreeMap$Node(java.lang.Object)"
                  [(.call "getKey" [])]))
              (.seq
                .skip
                (.seq
                  (.assign
                    "valuesEqual"
                    (.binop
                      "&&"
                      (.binop "!=" (.name "mine") (.lit .unit))
                      (.mcall
                        (.name "mine")
                        "value"
                        [(.field (.name "mine") "value"), (.call "getValue" [])])))
                  (.ret (.cond (.name "valuesEqual") (.name "mine") (.lit .unit))))))) }

/-- `com.google.gson.internal.LinkedTreeMap.equal:boolean(java.lang.Object,java.lang.Object)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_equal_boolean_java_lang_Object_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.equal:boolean(java.lang.Object,java.lang.Object)"
  , params := ["a", "b"]
  , body := (.ret (.call "equals" [(.name "a"), (.name "b")])) }

/-- `com.google.gson.internal.LinkedTreeMap.removeInternal:void(com.google.gson.internal.LinkedTreeMap$Node,boolean)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_removeInternal_void_com_google_gson_internal_LinkedTreeMap_Node_boolean_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.removeInternal:void(com.google.gson.internal.LinkedTreeMap$Node,boolean)"
  , params := ["this", "node", "unlink"]
  , body := (.seq
            (.ifte
              (.name "unlink")
              (.seq
                (.setField (.field (.name "node") "prev") "next" (.field (.name "node") "next"))
                (.setField (.field (.name "node") "next") "prev" (.field (.name "node") "prev")))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "left" (.field (.name "node") "left"))
                (.seq
                  .skip
                  (.seq
                    (.assign "right" (.field (.name "node") "right"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "originalParent" (.field (.name "node") "parent"))
                        (.seq
                          (.ifte
                            (.binop
                              "&&"
                              (.binop "!=" (.name "left") (.lit .unit))
                              (.binop "!=" (.name "right") (.lit .unit)))
                            (.seq
                              .skip
                              (.seq
                                (.assign
                                  "adjacent"
                                  (.cond
                                    (.binop
                                      ">"
                                      (.field (.name "left") "height")
                                      (.field (.name "right") "height"))
                                    (.call
                                      "com.google.gson.internal.LinkedTreeMap$Node.last:com.google.gson.internal.LinkedTreeMap$Node()"
                                      [])
                                    (.call
                                      "com.google.gson.internal.LinkedTreeMap$Node.first:com.google.gson.internal.LinkedTreeMap$Node()"
                                      [])))
                                (.seq
                                  (.expr
                                    (.call
                                      "com.google.gson.internal.LinkedTreeMap.removeInternal:void(com.google.gson.internal.LinkedTreeMap$Node,boolean)"
                                      [(.name "adjacent"), (.lit (.bool false))]))
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign "leftHeight" (.lit (.int 0)))
                                      (.seq
                                        (.assign "left" (.field (.name "node") "left"))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "left") (.lit .unit))
                                        (.seq
                                        (.assign "leftHeight" (.field (.name "left") "height"))
                                        (.seq
                                        (.setField (.name "adjacent") "left" (.name "left"))
                                        (.seq
                                        (.setField (.name "left") "parent" (.name "adjacent"))
                                        (.setField (.name "node") "left" (.lit .unit)))))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "rightHeight" (.lit (.int 0)))
                                        (.seq
                                        (.assign "right" (.field (.name "node") "right"))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "right") (.lit .unit))
                                        (.seq
                                        (.assign "rightHeight" (.field (.name "right") "height"))
                                        (.seq
                                        (.setField (.name "adjacent") "right" (.name "right"))
                                        (.seq
                                        (.setField (.name "right") "parent" (.name "adjacent"))
                                        (.setField (.name "node") "right" (.lit .unit)))))
                                        .skip)
                                        (.seq
                                        (.setField
                                        (.name "adjacent")
                                        "height"
                                        (.binop
                                        "+"
                                        (.call "max" [(.name "leftHeight"), (.name "rightHeight")])
                                        (.lit (.int 1))))
                                        (.seq
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.LinkedTreeMap.replaceInParent:void(com.google.gson.internal.LinkedTreeMap$Node,com.google.gson.internal.LinkedTreeMap$Node)"
                                        [(.name "node"), (.name "adjacent")]))
                                        (.ret (.lit .unit)))))))))))))))
                            (.ifte
                              (.binop "!=" (.name "left") (.lit .unit))
                              (.seq
                                (.expr
                                  (.call
                                    "com.google.gson.internal.LinkedTreeMap.replaceInParent:void(com.google.gson.internal.LinkedTreeMap$Node,com.google.gson.internal.LinkedTreeMap$Node)"
                                    [(.name "node"), (.name "left")]))
                                (.setField (.name "node") "left" (.lit .unit)))
                              (.ifte
                                (.binop "!=" (.name "right") (.lit .unit))
                                (.seq
                                  (.expr
                                    (.call
                                      "com.google.gson.internal.LinkedTreeMap.replaceInParent:void(com.google.gson.internal.LinkedTreeMap$Node,com.google.gson.internal.LinkedTreeMap$Node)"
                                      [(.name "node"), (.name "right")]))
                                  (.setField (.name "node") "right" (.lit .unit)))
                                (.expr
                                  (.call
                                    "com.google.gson.internal.LinkedTreeMap.replaceInParent:void(com.google.gson.internal.LinkedTreeMap$Node,com.google.gson.internal.LinkedTreeMap$Node)"
                                    [(.name "node"), (.lit .unit)])))))
                          (.seq
                            (.expr
                              (.call
                                "com.google.gson.internal.LinkedTreeMap.rebalance:void(com.google.gson.internal.LinkedTreeMap$Node,boolean)"
                                [(.name "originalParent"), (.lit (.bool false))]))
                            (.seq
                              (.expr (.hole "op:postDecrement"))
                              (.expr (.hole "op:postIncrement")))))))))))) }

/-- `com.google.gson.internal.LinkedTreeMap.removeInternalByKey:com.google.gson.internal.LinkedTreeMap$Node(java.lang.Object)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_removeInternalByKey_com_google_gson_internal_LinkedTreeMap_Node_java_lang_Objec : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.removeInternalByKey:com.google.gson.internal.LinkedTreeMap$Node(java.lang.Object)"
  , params := ["this", "key"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "node"
                (.call
                  "com.google.gson.internal.LinkedTreeMap.findByObject:com.google.gson.internal.LinkedTreeMap$Node(java.lang.Object)"
                  [(.name "key")]))
              (.seq
                (.ifte
                  (.binop "!=" (.name "node") (.lit .unit))
                  (.expr
                    (.call
                      "com.google.gson.internal.LinkedTreeMap.removeInternal:void(com.google.gson.internal.LinkedTreeMap$Node,boolean)"
                      [(.name "node"), (.lit (.bool true))]))
                  .skip)
                (.ret (.name "node"))))) }

/-- `com.google.gson.internal.LinkedTreeMap.replaceInParent:void(com.google.gson.internal.LinkedTreeMap$Node,com.google.gson.internal.LinkedTreeMap$Node)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_replaceInParent_void_com_google_gson_internal_LinkedTreeMap_Node_com_google_gso : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.replaceInParent:void(com.google.gson.internal.LinkedTreeMap$Node,com.google.gson.internal.LinkedTreeMap$Node)"
  , params := ["this", "node", "replacement"]
  , body := (.seq
            .skip
            (.seq
              (.assign "parent" (.field (.name "node") "parent"))
              (.seq
                (.setField (.name "node") "parent" (.lit .unit))
                (.seq
                  (.ifte
                    (.binop "!=" (.name "replacement") (.lit .unit))
                    (.setField (.name "replacement") "parent" (.name "parent"))
                    .skip)
                  (.ifte
                    (.binop "!=" (.name "parent") (.lit .unit))
                    (.ifte
                      (.binop "==" (.field (.name "parent") "left") (.name "node"))
                      (.setField (.name "parent") "left" (.name "replacement"))
                      (.seq
                        (.expr
                          (.call
                            "assert"
                            [(.binop "==" (.field (.name "parent") "right") (.name "node"))]))
                        (.setField (.name "parent") "right" (.name "replacement"))))
                    (.setField (.name "this") "root" (.name "replacement"))))))) }

/-- `com.google.gson.internal.LinkedTreeMap.rebalance:void(com.google.gson.internal.LinkedTreeMap$Node,boolean)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_rebalance_void_com_google_gson_internal_LinkedTreeMap_Node_boolean_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.rebalance:void(com.google.gson.internal.LinkedTreeMap$Node,boolean)"
  , params := ["this", "unbalanced", "insert"]
  , body := (.hole "control:FOR") }

/-- `com.google.gson.internal.LinkedTreeMap.rotateLeft:void(com.google.gson.internal.LinkedTreeMap$Node)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_rotateLeft_void_com_google_gson_internal_LinkedTreeMap_Node_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.rotateLeft:void(com.google.gson.internal.LinkedTreeMap$Node)"
  , params := ["this", "root"]
  , body := (.seq
            .skip
            (.seq
              (.assign "left" (.field (.name "root") "left"))
              (.seq
                .skip
                (.seq
                  (.assign "pivot" (.field (.name "root") "right"))
                  (.seq
                    .skip
                    (.seq
                      (.assign "pivotLeft" (.field (.name "pivot") "left"))
                      (.seq
                        .skip
                        (.seq
                          (.assign "pivotRight" (.field (.name "pivot") "right"))
                          (.seq
                            (.setField (.name "root") "right" (.name "pivotLeft"))
                            (.seq
                              (.ifte
                                (.binop "!=" (.name "pivotLeft") (.lit .unit))
                                (.setField (.name "pivotLeft") "parent" (.name "root"))
                                .skip)
                              (.seq
                                (.expr
                                  (.call
                                    "com.google.gson.internal.LinkedTreeMap.replaceInParent:void(com.google.gson.internal.LinkedTreeMap$Node,com.google.gson.internal.LinkedTreeMap$Node)"
                                    [(.name "root"), (.name "pivot")]))
                                (.seq
                                  (.setField (.name "pivot") "left" (.name "root"))
                                  (.seq
                                    (.setField (.name "root") "parent" (.name "pivot"))
                                    (.seq
                                      (.setField
                                        (.name "root")
                                        "height"
                                        (.binop
                                        "+"
                                        (.call
                                        "max"
                                        [ (.cond
                                        (.binop "!=" (.name "left") (.lit .unit))
                                        (.field (.name "left") "height")
                                        (.lit (.int 0)))
                                        , (.cond
                                        (.binop "!=" (.name "pivotLeft") (.lit .unit))
                                        (.field (.name "pivotLeft") "height")
                                        (.lit (.int 0))) ])
                                        (.lit (.int 1))))
                                      (.setField
                                        (.name "pivot")
                                        "height"
                                        (.binop
                                        "+"
                                        (.call
                                        "max"
                                        [ (.field (.name "root") "height")
                                        , (.cond
                                        (.binop "!=" (.name "pivotRight") (.lit .unit))
                                        (.field (.name "pivotRight") "height")
                                        (.lit (.int 0))) ])
                                        (.lit (.int 1)))))))))))))))))) }

/-- `com.google.gson.internal.LinkedTreeMap.rotateRight:void(com.google.gson.internal.LinkedTreeMap$Node)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_rotateRight_void_com_google_gson_internal_LinkedTreeMap_Node_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.rotateRight:void(com.google.gson.internal.LinkedTreeMap$Node)"
  , params := ["this", "root"]
  , body := (.seq
            .skip
            (.seq
              (.assign "pivot" (.field (.name "root") "left"))
              (.seq
                .skip
                (.seq
                  (.assign "right" (.field (.name "root") "right"))
                  (.seq
                    .skip
                    (.seq
                      (.assign "pivotLeft" (.field (.name "pivot") "left"))
                      (.seq
                        .skip
                        (.seq
                          (.assign "pivotRight" (.field (.name "pivot") "right"))
                          (.seq
                            (.setField (.name "root") "left" (.name "pivotRight"))
                            (.seq
                              (.ifte
                                (.binop "!=" (.name "pivotRight") (.lit .unit))
                                (.setField (.name "pivotRight") "parent" (.name "root"))
                                .skip)
                              (.seq
                                (.expr
                                  (.call
                                    "com.google.gson.internal.LinkedTreeMap.replaceInParent:void(com.google.gson.internal.LinkedTreeMap$Node,com.google.gson.internal.LinkedTreeMap$Node)"
                                    [(.name "root"), (.name "pivot")]))
                                (.seq
                                  (.setField (.name "pivot") "right" (.name "root"))
                                  (.seq
                                    (.setField (.name "root") "parent" (.name "pivot"))
                                    (.seq
                                      (.setField
                                        (.name "root")
                                        "height"
                                        (.binop
                                        "+"
                                        (.call
                                        "max"
                                        [ (.cond
                                        (.binop "!=" (.name "right") (.lit .unit))
                                        (.field (.name "right") "height")
                                        (.lit (.int 0)))
                                        , (.cond
                                        (.binop "!=" (.name "pivotRight") (.lit .unit))
                                        (.field (.name "pivotRight") "height")
                                        (.lit (.int 0))) ])
                                        (.lit (.int 1))))
                                      (.setField
                                        (.name "pivot")
                                        "height"
                                        (.binop
                                        "+"
                                        (.call
                                        "max"
                                        [ (.field (.name "root") "height")
                                        , (.cond
                                        (.binop "!=" (.name "pivotLeft") (.lit .unit))
                                        (.field (.name "pivotLeft") "height")
                                        (.lit (.int 0))) ])
                                        (.lit (.int 1)))))))))))))))))) }

/-- `com.google.gson.internal.LinkedTreeMap.entrySet:java.util.Set()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_entrySet_java_util_Set__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.entrySet:java.util.Set()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "result" (.field (.name "this") "entrySet"))
              (.seq
                (.ifte
                  (.binop "==" (.name "result") (.lit .unit))
                  (.seq
                    (.assign "result" (.hole "op:assignment"))
                    (.expr (.mcall (.name "this") "entrySet" [])))
                  .skip)
                (.ret (.name "result"))))) }

/-- `com.google.gson.internal.LinkedTreeMap.keySet:java.util.Set()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_keySet_java_util_Set__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.keySet:java.util.Set()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "result" (.field (.name "this") "keySet"))
              (.seq
                (.ifte
                  (.binop "==" (.name "result") (.lit .unit))
                  (.seq
                    (.assign "result" (.hole "op:assignment"))
                    (.expr (.mcall (.name "this") "keySet" [])))
                  .skip)
                (.ret (.name "result"))))) }

/-- `com.google.gson.internal.LinkedTreeMap$Node.<init>:void(boolean)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_Node__init__void_boolean_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$Node.<init>:void(boolean)"
  , params := ["this", "allowNullValue"]
  , body := (.seq
            (.setField (.name "this") "key" (.lit .unit))
            (.seq
              (.setField (.name "this") "allowNullValue" (.name "allowNullValue"))
              (.setField (.name "this") "next" (.hole "op:assignment")))) }

/-- `com.google.gson.internal.LinkedTreeMap$Node.<init>:void(boolean,com.google.gson.internal.LinkedTreeMap$Node,java.lang.Object,com.google.gson.internal.LinkedTreeMap$Node,com.google.gson.internal.LinkedTreeMap$Node)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_Node__init__void_boolean_com_google_gson_internal_LinkedTreeMap_Node_java_lang_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$Node.<init>:void(boolean,com.google.gson.internal.LinkedTreeMap$Node,java.lang.Object,com.google.gson.internal.LinkedTreeMap$Node,com.google.gson.internal.LinkedTreeMap$Node)"
  , params := ["this", "allowNullValue", "parent", "key", "next", "prev"]
  , body := (.seq
            (.setField (.name "this") "parent" (.name "parent"))
            (.seq
              (.setField (.name "this") "key" (.name "key"))
              (.seq
                (.setField (.name "this") "allowNullValue" (.name "allowNullValue"))
                (.seq
                  (.setField (.name "this") "height" (.lit (.int 1)))
                  (.seq
                    (.setField (.name "this") "next" (.name "next"))
                    (.seq
                      (.setField (.name "this") "prev" (.name "prev"))
                      (.seq
                        (.setField (.name "prev") "next" (.name "this"))
                        (.setField (.name "next") "prev" (.name "this"))))))))) }

/-- `com.google.gson.internal.LinkedTreeMap$Node.getKey:java.lang.Object()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_Node_getKey_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$Node.getKey:java.lang.Object()"
  , params := ["this"]
  , body := (.ret (.field (.name "this") "key")) }

/-- `com.google.gson.internal.LinkedTreeMap$Node.getValue:java.lang.Object()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_Node_getValue_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$Node.getValue:java.lang.Object()"
  , params := ["this"]
  , body := (.ret (.field (.name "this") "value")) }

/-- `com.google.gson.internal.LinkedTreeMap$Node.setValue:java.lang.Object(java.lang.Object)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_Node_setValue_java_lang_Object_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$Node.setValue:java.lang.Object(java.lang.Object)"
  , params := ["this", "value"]
  , body := (.seq
            (.ifte
              (.binop
                "&&"
                (.binop "==" (.name "value") (.lit .unit))
                (.unop "!" (.field (.name "this") "allowNullValue")))
              (.hole "control:THROW")
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "oldValue" (.field (.name "this") "value"))
                (.seq (.setField (.name "this") "value" (.name "value")) (.ret (.name "oldValue")))))) }

/-- `com.google.gson.internal.LinkedTreeMap$Node.equals:boolean(java.lang.Object)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_Node_equals_boolean_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$Node.equals:boolean(java.lang.Object)"
  , params := ["this", "o"]
  , body := (.seq
            (.ifte
              (.hole "op:instanceOf")
              (.seq
                .skip
                (.seq
                  (.assign "other" (.hole "op:cast"))
                  (.ret
                    (.binop
                      "&&"
                      (.cond
                        (.binop "==" (.field (.name "this") "key") (.lit .unit))
                        (.binop "==" (.call "getKey" []) (.lit .unit))
                        (.mcall (.name "this") "key" [(.call "getKey" [])]))
                      (.cond
                        (.binop "==" (.field (.name "this") "value") (.lit .unit))
                        (.binop "==" (.call "getValue" []) (.lit .unit))
                        (.mcall (.name "this") "value" [(.call "getValue" [])]))))))
              .skip)
            (.ret (.lit (.bool false)))) }

/-- `com.google.gson.internal.LinkedTreeMap$Node.hashCode:int()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_Node_hashCode_int__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$Node.hashCode:int()"
  , params := ["this"]
  , body := (.ret (.hole "op:xor")) }

/-- `com.google.gson.internal.LinkedTreeMap$Node.toString:java.lang.String()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_Node_toString_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$Node.toString:java.lang.String()"
  , params := ["this"]
  , body := (.ret
            (.binop
              "+"
              (.binop "+" (.field (.name "this") "key") (.lit (.str "=")))
              (.field (.name "this") "value"))) }

/-- `com.google.gson.internal.LinkedTreeMap$Node.first:com.google.gson.internal.LinkedTreeMap$Node()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_Node_first_com_google_gson_internal_LinkedTreeMap_Node__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$Node.first:com.google.gson.internal.LinkedTreeMap$Node()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "node" (.name "this"))
              (.seq
                .skip
                (.seq
                  (.assign "child" (.field (.name "node") "left"))
                  (.seq
                    (.loop
                      (.binop "!=" (.name "child") (.lit .unit))
                      (.seq
                        (.assign "node" (.name "child"))
                        (.assign "child" (.field (.name "node") "left"))))
                    (.ret (.name "node"))))))) }

/-- `com.google.gson.internal.LinkedTreeMap$Node.last:com.google.gson.internal.LinkedTreeMap$Node()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_Node_last_com_google_gson_internal_LinkedTreeMap_Node__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$Node.last:com.google.gson.internal.LinkedTreeMap$Node()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "node" (.name "this"))
              (.seq
                .skip
                (.seq
                  (.assign "child" (.field (.name "node") "right"))
                  (.seq
                    (.loop
                      (.binop "!=" (.name "child") (.lit .unit))
                      (.seq
                        (.assign "node" (.name "child"))
                        (.assign "child" (.field (.name "node") "right"))))
                    (.ret (.name "node"))))))) }

/-- `com.google.gson.internal.LinkedTreeMap$LinkedTreeMapIterator.<init>:void()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_LinkedTreeMapIterator__init__void__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$LinkedTreeMapIterator.<init>:void()"
  , params := ["this", "outerClass"]
  , body := (.seq
            (.setField (.name "this") "outerClass" (.name "outerClass"))
            (.seq
              (.setField
                (.name "this")
                "next"
                (.field (.field (.field (.name "this") "outerClass") "header") "next"))
              (.seq
                (.setField (.name "this") "lastReturned" (.lit .unit))
                (.setField
                  (.name "this")
                  "expectedModCount"
                  (.field (.field (.name "this") "outerClass") "modCount"))))) }

/-- `com.google.gson.internal.LinkedTreeMap$LinkedTreeMapIterator.hasNext:boolean()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_LinkedTreeMapIterator_hasNext_boolean__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$LinkedTreeMapIterator.hasNext:boolean()"
  , params := ["this"]
  , body := (.ret
            (.binop
              "!="
              (.field (.name "this") "next")
              (.field (.field (.name "this") "outerClass") "header"))) }

/-- `com.google.gson.internal.LinkedTreeMap$LinkedTreeMapIterator.nextNode:com.google.gson.internal.LinkedTreeMap$Node()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_LinkedTreeMapIterator_nextNode_com_google_gson_internal_LinkedTreeMap_Node__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$LinkedTreeMapIterator.nextNode:com.google.gson.internal.LinkedTreeMap$Node()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "e" (.field (.name "this") "next"))
              (.seq
                (.ifte
                  (.binop "==" (.name "e") (.field (.field (.name "this") "outerClass") "header"))
                  (.hole "control:THROW")
                  .skip)
                (.seq
                  (.ifte
                    (.binop
                      "!="
                      (.field (.field (.name "this") "outerClass") "modCount")
                      (.field (.name "this") "expectedModCount"))
                    (.hole "control:THROW")
                    .skip)
                  (.seq
                    (.setField (.name "this") "next" (.field (.name "e") "next"))
                    (.seq (.setField (.name "this") "lastReturned" (.name "e")) (.ret (.name "e")))))))) }

/-- `com.google.gson.internal.LinkedTreeMap$LinkedTreeMapIterator.remove:void()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_LinkedTreeMapIterator_remove_void__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$LinkedTreeMapIterator.remove:void()"
  , params := ["this"]
  , body := (.seq
            (.ifte
              (.binop "==" (.field (.name "this") "lastReturned") (.lit .unit))
              (.hole "control:THROW")
              .skip)
            (.seq
              (.expr
                (.mcall
                  (.name "this")
                  "outerClass"
                  [(.field (.name "this") "lastReturned"), (.lit (.bool true))]))
              (.seq
                (.setField (.name "this") "lastReturned" (.lit .unit))
                (.setField
                  (.name "this")
                  "expectedModCount"
                  (.field (.field (.name "this") "outerClass") "modCount"))))) }

/-- `com.google.gson.internal.LinkedTreeMap$EntrySet.size:int()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_EntrySet_size_int__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$EntrySet.size:int()"
  , params := ["this"]
  , body := (.ret (.field (.field (.name "this") "outerClass") "size")) }

/-- `com.google.gson.internal.LinkedTreeMap$EntrySet.iterator:java.util.Iterator()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_EntrySet_iterator_java_util_Iterator__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$EntrySet.iterator:java.util.Iterator()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj7" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.LinkedTreeMap$EntrySet.iterator.LinkedTreeMapIterator$0.<init>:void()"
                    [(.name "this")]))
                (.ret (.name "$obj7"))))) }

/-- `com.google.gson.internal.LinkedTreeMap$EntrySet.contains:boolean(java.lang.Object)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_EntrySet_contains_boolean_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$EntrySet.contains:boolean(java.lang.Object)"
  , params := ["this", "o"]
  , body := (.ret
            (.binop
              "&&"
              (.hole "op:instanceOf")
              (.binop "!=" (.mcall (.name "this") "outerClass" [(.hole "op:cast")]) (.lit .unit)))) }

/-- `com.google.gson.internal.LinkedTreeMap$EntrySet.remove:boolean(java.lang.Object)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_EntrySet_remove_boolean_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$EntrySet.remove:boolean(java.lang.Object)"
  , params := ["this", "o"]
  , body := (.seq
            (.ifte (.unop "!" (.hole "op:instanceOf")) (.ret (.lit (.bool false))) .skip)
            (.seq
              .skip
              (.seq
                (.assign "node" (.mcall (.name "this") "outerClass" [(.hole "op:cast")]))
                (.seq
                  (.ifte
                    (.binop "==" (.name "node") (.lit .unit))
                    (.ret (.lit (.bool false)))
                    .skip)
                  (.seq
                    (.expr
                      (.mcall (.name "this") "outerClass" [(.name "node"), (.lit (.bool true))]))
                    (.ret (.lit (.bool true)))))))) }

/-- `com.google.gson.internal.LinkedTreeMap$EntrySet.clear:void()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_EntrySet_clear_void__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$EntrySet.clear:void()"
  , params := ["this"]
  , body := (.expr (.call "com.google.gson.internal.LinkedTreeMap.clear:void()" [])) }

/-- `com.google.gson.internal.LinkedTreeMap$EntrySet.<init>:void()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_EntrySet__init__void__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$EntrySet.<init>:void()"
  , params := ["this", "outerClass"]
  , body := (.setField (.name "this") "outerClass" (.name "outerClass")) }

/-- `com.google.gson.internal.LinkedTreeMap$EntrySet.iterator.LinkedTreeMapIterator$0.next:java.util.Map$Entry()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_EntrySet_iterator_LinkedTreeMapIterator_0_next_java_util_Map_Entry__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$EntrySet.iterator.LinkedTreeMapIterator$0.next:java.util.Map$Entry()"
  , params := ["this"]
  , body := (.ret (.call "nextNode" [])) }

/-- `com.google.gson.internal.LinkedTreeMap$EntrySet.iterator.LinkedTreeMapIterator$0.<init>:void()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_EntrySet_iterator_LinkedTreeMapIterator_0__init__void__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$EntrySet.iterator.LinkedTreeMapIterator$0.<init>:void()"
  , params := ["this", "outerClass"]
  , body := (.setField (.name "this") "outerClass" (.name "outerClass")) }

/-- `com.google.gson.internal.LinkedTreeMap$KeySet.size:int()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_KeySet_size_int__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$KeySet.size:int()"
  , params := ["this"]
  , body := (.ret (.field (.field (.name "this") "outerClass") "size")) }

/-- `com.google.gson.internal.LinkedTreeMap$KeySet.iterator:java.util.Iterator()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_KeySet_iterator_java_util_Iterator__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$KeySet.iterator:java.util.Iterator()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj8" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.LinkedTreeMap$KeySet.iterator.LinkedTreeMapIterator$0.<init>:void()"
                    [(.name "this")]))
                (.ret (.name "$obj8"))))) }

/-- `com.google.gson.internal.LinkedTreeMap$KeySet.contains:boolean(java.lang.Object)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_KeySet_contains_boolean_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$KeySet.contains:boolean(java.lang.Object)"
  , params := ["this", "o"]
  , body := (.ret (.mcall (.name "this") "outerClass" [(.name "o")])) }

/-- `com.google.gson.internal.LinkedTreeMap$KeySet.remove:boolean(java.lang.Object)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_KeySet_remove_boolean_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$KeySet.remove:boolean(java.lang.Object)"
  , params := ["this", "key"]
  , body := (.ret (.binop "!=" (.mcall (.name "this") "outerClass" [(.name "key")]) (.lit .unit))) }

/-- `com.google.gson.internal.LinkedTreeMap$KeySet.clear:void()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_KeySet_clear_void__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$KeySet.clear:void()"
  , params := ["this"]
  , body := (.expr (.call "com.google.gson.internal.LinkedTreeMap.clear:void()" [])) }

/-- `com.google.gson.internal.LinkedTreeMap$KeySet.<init>:void()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_KeySet__init__void__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$KeySet.<init>:void()"
  , params := ["this", "outerClass"]
  , body := (.setField (.name "this") "outerClass" (.name "outerClass")) }

/-- `com.google.gson.internal.LinkedTreeMap$KeySet.iterator.LinkedTreeMapIterator$0.next:java.lang.Object()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_KeySet_iterator_LinkedTreeMapIterator_0_next_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$KeySet.iterator.LinkedTreeMapIterator$0.next:java.lang.Object()"
  , params := ["this"]
  , body := (.ret (.field (.call "nextNode" []) "key")) }

/-- `com.google.gson.internal.LinkedTreeMap$KeySet.iterator.LinkedTreeMapIterator$0.<init>:void()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_KeySet_iterator_LinkedTreeMapIterator_0__init__void__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap$KeySet.iterator.LinkedTreeMapIterator$0.<init>:void()"
  , params := ["this", "outerClass"]
  , body := (.setField (.name "this") "outerClass" (.name "outerClass")) }

/-- `com.google.gson.internal.LinkedTreeMap.writeReplace:java.lang.Object()`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_writeReplace_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.writeReplace:java.lang.Object()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj9" (.hole "op:alloc"))
              (.seq (.expr (.call "<init>" [(.name "this")])) (.ret (.name "$obj9"))))) }

/-- `com.google.gson.internal.LinkedTreeMap.readObject:void(java.io.ObjectInputStream)`  (from `internal/LinkedTreeMap.java`) -/
def f_com_google_gson_internal_LinkedTreeMap_readObject_void_java_io_ObjectInputStream_ : Func :=
  { name := "com.google.gson.internal.LinkedTreeMap.readObject:void(java.io.ObjectInputStream)"
  , params := ["this", "in"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.NonNullElementWrapperList.<init>:void(java.util.ArrayList)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList__init__void_java_util_ArrayList_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.<init>:void(java.util.ArrayList)"
  , params := ["this", "delegate"]
  , body := (.setField (.name "this") "delegate" (.call "requireNonNull" [(.name "delegate")])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.get:java.lang.Object(int)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_get_java_lang_Object_int_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.get:java.lang.Object(int)"
  , params := ["this", "index"]
  , body := (.ret (.mcall (.name "this") "delegate" [(.name "index")])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.size:int()`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_size_int__ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.size:int()"
  , params := ["this"]
  , body := (.ret (.mcall (.name "this") "delegate" [])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.nonNull:java.lang.Object(java.lang.Object)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_nonNull_java_lang_Object_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.nonNull:java.lang.Object(java.lang.Object)"
  , params := ["this", "element"]
  , body := (.seq
            (.ifte (.binop "==" (.name "element") (.lit .unit)) (.hole "control:THROW") .skip)
            (.ret (.name "element"))) }

/-- `com.google.gson.internal.NonNullElementWrapperList.set:java.lang.Object(int,java.lang.Object)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_set_java_lang_Object_int_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.set:java.lang.Object(int,java.lang.Object)"
  , params := ["this", "index", "element"]
  , body := (.ret
            (.mcall
              (.name "this")
              "delegate"
              [ (.name "index")
              , (.call
                  "com.google.gson.internal.NonNullElementWrapperList.nonNull:java.lang.Object(java.lang.Object)"
                  [(.name "element")]) ])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.add:void(int,java.lang.Object)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_add_void_int_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.add:void(int,java.lang.Object)"
  , params := ["this", "index", "element"]
  , body := (.expr
            (.mcall
              (.name "this")
              "delegate"
              [ (.name "index")
              , (.call
                  "com.google.gson.internal.NonNullElementWrapperList.nonNull:java.lang.Object(java.lang.Object)"
                  [(.name "element")]) ])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.remove:java.lang.Object(int)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_remove_java_lang_Object_int_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.remove:java.lang.Object(int)"
  , params := ["this", "index"]
  , body := (.ret (.mcall (.name "this") "delegate" [(.name "index")])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.clear:void()`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_clear_void__ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.clear:void()"
  , params := ["this"]
  , body := (.expr (.mcall (.name "this") "delegate" [])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.remove:boolean(java.lang.Object)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_remove_boolean_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.remove:boolean(java.lang.Object)"
  , params := ["this", "o"]
  , body := (.ret (.mcall (.name "this") "delegate" [(.name "o")])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.removeAll:boolean(java.util.Collection)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_removeAll_boolean_java_util_Collection_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.removeAll:boolean(java.util.Collection)"
  , params := ["this", "c"]
  , body := (.ret (.mcall (.name "this") "delegate" [(.name "c")])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.retainAll:boolean(java.util.Collection)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_retainAll_boolean_java_util_Collection_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.retainAll:boolean(java.util.Collection)"
  , params := ["this", "c"]
  , body := (.ret (.mcall (.name "this") "delegate" [(.name "c")])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.contains:boolean(java.lang.Object)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_contains_boolean_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.contains:boolean(java.lang.Object)"
  , params := ["this", "o"]
  , body := (.ret (.mcall (.name "this") "delegate" [(.name "o")])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.indexOf:int(java.lang.Object)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_indexOf_int_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.indexOf:int(java.lang.Object)"
  , params := ["this", "o"]
  , body := (.ret (.mcall (.name "this") "delegate" [(.name "o")])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.lastIndexOf:int(java.lang.Object)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_lastIndexOf_int_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.lastIndexOf:int(java.lang.Object)"
  , params := ["this", "o"]
  , body := (.ret (.mcall (.name "this") "delegate" [(.name "o")])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.toArray:java.lang.Object[]()`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_toArray_java_lang_Object____ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.toArray:java.lang.Object[]()"
  , params := ["this"]
  , body := (.ret (.mcall (.name "this") "delegate" [])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.toArray:java.lang.Object[](java.lang.Object[])`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_toArray_java_lang_Object___java_lang_Object___ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.toArray:java.lang.Object[](java.lang.Object[])"
  , params := ["this", "a"]
  , body := (.ret (.mcall (.name "this") "delegate" [(.name "a")])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.sort:void(java.util.Comparator)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_sort_void_java_util_Comparator_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.sort:void(java.util.Comparator)"
  , params := ["this", "c"]
  , body := (.expr (.mcall (.name "this") "delegate" [(.name "c")])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.spliterator:java.util.Spliterator()`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_spliterator_java_util_Spliterator__ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.spliterator:java.util.Spliterator()"
  , params := ["this"]
  , body := (.ret (.mcall (.name "this") "delegate" [])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.equals:boolean(java.lang.Object)`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_equals_boolean_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.equals:boolean(java.lang.Object)"
  , params := ["this", "o"]
  , body := (.ret (.mcall (.name "this") "delegate" [(.name "o")])) }

/-- `com.google.gson.internal.NonNullElementWrapperList.hashCode:int()`  (from `internal/NonNullElementWrapperList.java`) -/
def f_com_google_gson_internal_NonNullElementWrapperList_hashCode_int__ : Func :=
  { name := "com.google.gson.internal.NonNullElementWrapperList.hashCode:int()"
  , params := ["this"]
  , body := (.ret (.mcall (.name "this") "delegate" [])) }

/-- `com.google.gson.internal.NumberLimits.<init>:void()`  (from `internal/NumberLimits.java`) -/
def f_com_google_gson_internal_NumberLimits__init__void__ : Func :=
  { name := "com.google.gson.internal.NumberLimits.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.NumberLimits.checkNumberStringLength:void(java.lang.String)`  (from `internal/NumberLimits.java`) -/
def f_com_google_gson_internal_NumberLimits_checkNumberStringLength_void_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.NumberLimits.checkNumberStringLength:void(java.lang.String)"
  , params := ["s"]
  , body := (.ifte
            (.binop
              ">"
              (.call "length" [])
              (.field (.fnref "com.google.gson.internal.NumberLimits") "MAX_NUMBER_STRING_LENGTH"))
            (.hole "control:THROW")
            .skip) }

/-- `com.google.gson.internal.NumberLimits.parseBigDecimal:java.math.BigDecimal(java.lang.String)`  (from `internal/NumberLimits.java`) -/
def f_com_google_gson_internal_NumberLimits_parseBigDecimal_java_math_BigDecimal_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.NumberLimits.parseBigDecimal:java.math.BigDecimal(java.lang.String)"
  , params := ["s"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.NumberLimits.checkNumberStringLength:void(java.lang.String)"
                [(.name "s")]))
            (.seq
              .skip
              (.seq
                (.assign "decimal" (.hole "op:alloc"))
                (.seq
                  (.expr (.call "<init>" [(.name "s")]))
                  (.seq
                    (.ifte
                      (.binop ">=" (.call "abs" [(.hole "op:cast")]) (.hole "lit:unquoted"))
                      (.hole "control:THROW")
                      .skip)
                    (.ret (.name "decimal"))))))) }

/-- `com.google.gson.internal.NumberLimits.parseBigInteger:java.math.BigInteger(java.lang.String)`  (from `internal/NumberLimits.java`) -/
def f_com_google_gson_internal_NumberLimits_parseBigInteger_java_math_BigInteger_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.NumberLimits.parseBigInteger:java.math.BigInteger(java.lang.String)"
  , params := ["s"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.NumberLimits.checkNumberStringLength:void(java.lang.String)"
                [(.name "s")]))
            (.seq
              .skip
              (.seq
                (.assign "$obj2" (.hole "op:alloc"))
                (.seq (.expr (.call "<init>" [(.name "s")])) (.ret (.name "$obj2")))))) }

/-- `com.google.gson.internal.NumberLimits.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_NumberLimits__clinit__void__ : Func :=
  { name := "com.google.gson.internal.NumberLimits.<clinit>:void()"
  , params := []
  , body := (.setField
            (.fnref "com.google.gson.internal.NumberLimits")
            "MAX_NUMBER_STRING_LENGTH"
            (.hole "lit:unquoted")) }

/-- `com.google.gson.internal.ObjectConstructor.construct:java.lang.Object()`  (from `internal/ObjectConstructor.java`) -/
def f_com_google_gson_internal_ObjectConstructor_construct_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.ObjectConstructor.construct:java.lang.Object()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.PreJava9DateFormatProvider.<init>:void()`  (from `internal/PreJava9DateFormatProvider.java`) -/
def f_com_google_gson_internal_PreJava9DateFormatProvider__init__void__ : Func :=
  { name := "com.google.gson.internal.PreJava9DateFormatProvider.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.PreJava9DateFormatProvider.getUsDateTimeFormat:java.text.DateFormat(int,int)`  (from `internal/PreJava9DateFormatProvider.java`) -/
def f_com_google_gson_internal_PreJava9DateFormatProvider_getUsDateTimeFormat_java_text_DateFormat_int_int_ : Func :=
  { name := "com.google.gson.internal.PreJava9DateFormatProvider.getUsDateTimeFormat:java.text.DateFormat(int,int)"
  , params := ["dateStyle", "timeStyle"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "pattern"
                (.binop
                  "+"
                  (.binop
                    "+"
                    (.call
                      "com.google.gson.internal.PreJava9DateFormatProvider.getDatePartOfDateTimePattern:java.lang.String(int)"
                      [(.name "dateStyle")])
                    (.lit (.str " ")))
                  (.call
                    "com.google.gson.internal.PreJava9DateFormatProvider.getTimePartOfDateTimePattern:java.lang.String(int)"
                    [(.name "timeStyle")])))
              (.seq
                .skip
                (.seq
                  (.assign "$obj0" (.hole "op:alloc"))
                  (.seq
                    (.expr (.call "<init>" [(.name "pattern"), (.field (.name "Locale") "US")]))
                    (.ret (.name "$obj0"))))))) }

/-- `com.google.gson.internal.PreJava9DateFormatProvider.getDatePartOfDateTimePattern:java.lang.String(int)`  (from `internal/PreJava9DateFormatProvider.java`) -/
def f_com_google_gson_internal_PreJava9DateFormatProvider_getDatePartOfDateTimePattern_java_lang_String_int_ : Func :=
  { name := "com.google.gson.internal.PreJava9DateFormatProvider.getDatePartOfDateTimePattern:java.lang.String(int)"
  , params := ["dateStyle"]
  , body := (.hole "control:SWITCH") }

/-- `com.google.gson.internal.PreJava9DateFormatProvider.getTimePartOfDateTimePattern:java.lang.String(int)`  (from `internal/PreJava9DateFormatProvider.java`) -/
def f_com_google_gson_internal_PreJava9DateFormatProvider_getTimePartOfDateTimePattern_java_lang_String_int_ : Func :=
  { name := "com.google.gson.internal.PreJava9DateFormatProvider.getTimePartOfDateTimePattern:java.lang.String(int)"
  , params := ["timeStyle"]
  , body := (.hole "control:SWITCH") }

/-- `com.google.gson.internal.Primitives.<init>:void()`  (from `internal/Primitives.java`) -/
def f_com_google_gson_internal_Primitives__init__void__ : Func :=
  { name := "com.google.gson.internal.Primitives.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.Primitives.isPrimitive:boolean(java.lang.reflect.Type)`  (from `internal/Primitives.java`) -/
def f_com_google_gson_internal_Primitives_isPrimitive_boolean_java_lang_reflect_Type_ : Func :=
  { name := "com.google.gson.internal.Primitives.isPrimitive:boolean(java.lang.reflect.Type)"
  , params := ["type"]
  , body := (.ret (.binop "&&" (.hole "op:instanceOf") (.call "isPrimitive" []))) }

/-- `com.google.gson.internal.Primitives.isWrapperType:boolean(java.lang.reflect.Type)`  (from `internal/Primitives.java`) -/
def f_com_google_gson_internal_Primitives_isWrapperType_boolean_java_lang_reflect_Type_ : Func :=
  { name := "com.google.gson.internal.Primitives.isWrapperType:boolean(java.lang.reflect.Type)"
  , params := ["type"]
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
                          (.binop
                            "||"
                            (.binop "==" (.name "type") (.field (.name "Integer") "class"))
                            (.binop "==" (.name "type") (.field (.name "Float") "class")))
                          (.binop "==" (.name "type") (.field (.name "Byte") "class")))
                        (.binop "==" (.name "type") (.field (.name "Double") "class")))
                      (.binop "==" (.name "type") (.field (.name "Long") "class")))
                    (.binop "==" (.name "type") (.field (.name "Character") "class")))
                  (.binop "==" (.name "type") (.field (.name "Boolean") "class")))
                (.binop "==" (.name "type") (.field (.name "Short") "class")))
              (.binop "==" (.name "type") (.field (.name "Void") "class")))) }

/-- `com.google.gson.internal.Primitives.wrap:java.lang.Class(java.lang.Class)`  (from `internal/Primitives.java`) -/
def f_com_google_gson_internal_Primitives_wrap_java_lang_Class_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.Primitives.wrap:java.lang.Class(java.lang.Class)"
  , params := ["type"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "type") (.field (.name "int") "class"))
              (.ret (.hole "op:cast"))
              .skip)
            (.seq
              (.ifte
                (.binop "==" (.name "type") (.field (.name "float") "class"))
                (.ret (.hole "op:cast"))
                .skip)
              (.seq
                (.ifte
                  (.binop "==" (.name "type") (.field (.name "byte") "class"))
                  (.ret (.hole "op:cast"))
                  .skip)
                (.seq
                  (.ifte
                    (.binop "==" (.name "type") (.field (.name "double") "class"))
                    (.ret (.hole "op:cast"))
                    .skip)
                  (.seq
                    (.ifte
                      (.binop "==" (.name "type") (.field (.name "long") "class"))
                      (.ret (.hole "op:cast"))
                      .skip)
                    (.seq
                      (.ifte
                        (.binop "==" (.name "type") (.field (.name "char") "class"))
                        (.ret (.hole "op:cast"))
                        .skip)
                      (.seq
                        (.ifte
                          (.binop "==" (.name "type") (.field (.name "boolean") "class"))
                          (.ret (.hole "op:cast"))
                          .skip)
                        (.seq
                          (.ifte
                            (.binop "==" (.name "type") (.field (.name "short") "class"))
                            (.ret (.hole "op:cast"))
                            .skip)
                          (.seq
                            (.ifte
                              (.binop "==" (.name "type") (.field (.name "void") "class"))
                              (.ret (.hole "op:cast"))
                              .skip)
                            (.ret (.name "type"))))))))))) }

/-- `com.google.gson.internal.Primitives.unwrap:java.lang.Class(java.lang.Class)`  (from `internal/Primitives.java`) -/
def f_com_google_gson_internal_Primitives_unwrap_java_lang_Class_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.Primitives.unwrap:java.lang.Class(java.lang.Class)"
  , params := ["type"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "type") (.field (.name "Integer") "class"))
              (.ret (.hole "op:cast"))
              .skip)
            (.seq
              (.ifte
                (.binop "==" (.name "type") (.field (.name "Float") "class"))
                (.ret (.hole "op:cast"))
                .skip)
              (.seq
                (.ifte
                  (.binop "==" (.name "type") (.field (.name "Byte") "class"))
                  (.ret (.hole "op:cast"))
                  .skip)
                (.seq
                  (.ifte
                    (.binop "==" (.name "type") (.field (.name "Double") "class"))
                    (.ret (.hole "op:cast"))
                    .skip)
                  (.seq
                    (.ifte
                      (.binop "==" (.name "type") (.field (.name "Long") "class"))
                      (.ret (.hole "op:cast"))
                      .skip)
                    (.seq
                      (.ifte
                        (.binop "==" (.name "type") (.field (.name "Character") "class"))
                        (.ret (.hole "op:cast"))
                        .skip)
                      (.seq
                        (.ifte
                          (.binop "==" (.name "type") (.field (.name "Boolean") "class"))
                          (.ret (.hole "op:cast"))
                          .skip)
                        (.seq
                          (.ifte
                            (.binop "==" (.name "type") (.field (.name "Short") "class"))
                            (.ret (.hole "op:cast"))
                            .skip)
                          (.seq
                            (.ifte
                              (.binop "==" (.name "type") (.field (.name "Void") "class"))
                              (.ret (.hole "op:cast"))
                              .skip)
                            (.ret (.name "type"))))))))))) }

/-- `com.google.gson.internal.ReflectionAccessFilterHelper.<init>:void()`  (from `internal/ReflectionAccessFilterHelper.java`) -/
def f_com_google_gson_internal_ReflectionAccessFilterHelper__init__void__ : Func :=
  { name := "com.google.gson.internal.ReflectionAccessFilterHelper.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.ReflectionAccessFilterHelper.isJavaType:boolean(java.lang.Class)`  (from `internal/ReflectionAccessFilterHelper.java`) -/
def f_com_google_gson_internal_ReflectionAccessFilterHelper_isJavaType_boolean_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.ReflectionAccessFilterHelper.isJavaType:boolean(java.lang.Class)"
  , params := ["c"]
  , body := (.ret
            (.call
              "com.google.gson.internal.ReflectionAccessFilterHelper.isJavaType:boolean(java.lang.String)"
              [(.call "getName" [])])) }

/-- `com.google.gson.internal.ReflectionAccessFilterHelper.isJavaType:boolean(java.lang.String)`  (from `internal/ReflectionAccessFilterHelper.java`) -/
def f_com_google_gson_internal_ReflectionAccessFilterHelper_isJavaType_boolean_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.ReflectionAccessFilterHelper.isJavaType:boolean(java.lang.String)"
  , params := ["className"]
  , body := (.ret
            (.binop
              "||"
              (.call "startsWith" [(.lit (.str "java."))])
              (.call "startsWith" [(.lit (.str "javax."))]))) }

/-- `com.google.gson.internal.ReflectionAccessFilterHelper.isAndroidType:boolean(java.lang.Class)`  (from `internal/ReflectionAccessFilterHelper.java`) -/
def f_com_google_gson_internal_ReflectionAccessFilterHelper_isAndroidType_boolean_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.ReflectionAccessFilterHelper.isAndroidType:boolean(java.lang.Class)"
  , params := ["c"]
  , body := (.ret
            (.call
              "com.google.gson.internal.ReflectionAccessFilterHelper.isAndroidType:boolean(java.lang.String)"
              [(.call "getName" [])])) }

/-- `com.google.gson.internal.ReflectionAccessFilterHelper.isAndroidType:boolean(java.lang.String)`  (from `internal/ReflectionAccessFilterHelper.java`) -/
def f_com_google_gson_internal_ReflectionAccessFilterHelper_isAndroidType_boolean_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.ReflectionAccessFilterHelper.isAndroidType:boolean(java.lang.String)"
  , params := ["className"]
  , body := (.ret
            (.binop
              "||"
              (.binop
                "||"
                (.call "startsWith" [(.lit (.str "android."))])
                (.call "startsWith" [(.lit (.str "androidx."))]))
              (.call
                "com.google.gson.internal.ReflectionAccessFilterHelper.isJavaType:boolean(java.lang.String)"
                [(.name "className")]))) }

/-- `com.google.gson.internal.ReflectionAccessFilterHelper.isAnyPlatformType:boolean(java.lang.Class)`  (from `internal/ReflectionAccessFilterHelper.java`) -/
def f_com_google_gson_internal_ReflectionAccessFilterHelper_isAnyPlatformType_boolean_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.ReflectionAccessFilterHelper.isAnyPlatformType:boolean(java.lang.Class)"
  , params := ["c"]
  , body := (.seq
            .skip
            (.seq
              (.assign "className" (.call "getName" []))
              (.ret
                (.binop
                  "||"
                  (.binop
                    "||"
                    (.binop
                      "||"
                      (.call
                        "com.google.gson.internal.ReflectionAccessFilterHelper.isAndroidType:boolean(java.lang.String)"
                        [(.name "className")])
                      (.call "startsWith" [(.lit (.str "kotlin."))]))
                    (.call "startsWith" [(.lit (.str "kotlinx."))]))
                  (.call "startsWith" [(.lit (.str "scala."))]))))) }

/-- `com.google.gson.internal.ReflectionAccessFilterHelper.getFilterResult:com.google.gson.ReflectionAccessFilter.FilterResult(java.util.List,java.lang.Class)`  (from `internal/ReflectionAccessFilterHelper.java`) -/
def f_com_google_gson_internal_ReflectionAccessFilterHelper_getFilterResult_com_google_gson_ReflectionAccessFilter_FilterRes : Func :=
  { name := "com.google.gson.internal.ReflectionAccessFilterHelper.getFilterResult:com.google.gson.ReflectionAccessFilter.FilterResult(java.util.List,java.lang.Class)"
  , params := ["reflectionFilters", "c"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$iterLocal0" (.call "iterator" []))
              (.seq
                (.loop
                  (.call "hasNext" [])
                  (.seq
                    .skip
                    (.seq
                      (.assign "filter" (.call "next" []))
                      (.seq
                        .skip
                        (.seq
                          (.assign "result" (.call "check" [(.name "c")]))
                          (.ifte
                            (.binop
                              "!="
                              (.name "result")
                              (.field (.name "FilterResult") "INDECISIVE"))
                            (.ret (.name "result"))
                            .skip))))))
                (.ret (.field (.name "FilterResult") "ALLOW"))))) }

/-- `com.google.gson.internal.ReflectionAccessFilterHelper.canAccess:boolean(java.lang.reflect.AccessibleObject,java.lang.Object)`  (from `internal/ReflectionAccessFilterHelper.java`) -/
def f_com_google_gson_internal_ReflectionAccessFilterHelper_canAccess_boolean_java_lang_reflect_AccessibleObject_java_lang_O : Func :=
  { name := "com.google.gson.internal.ReflectionAccessFilterHelper.canAccess:boolean(java.lang.reflect.AccessibleObject,java.lang.Object)"
  , params := ["accessibleObject", "object"]
  , body := (.ret
            (.mcall
              (.name "AccessChecker")
              "INSTANCE"
              [(.name "accessibleObject"), (.name "object")])) }

/-- `com.google.gson.internal.ReflectionAccessFilterHelper$AccessChecker.canAccess:boolean(java.lang.reflect.AccessibleObject,java.lang.Object)`  (from `internal/ReflectionAccessFilterHelper.java`) -/
def f_com_google_gson_internal_ReflectionAccessFilterHelper_AccessChecker_canAccess_boolean_java_lang_reflect_AccessibleObje : Func :=
  { name := "com.google.gson.internal.ReflectionAccessFilterHelper$AccessChecker.canAccess:boolean(java.lang.reflect.AccessibleObject,java.lang.Object)"
  , params := ["this", "accessibleObject", "object"]
  , body := .skip }

/-- `com.google.gson.internal.ReflectionAccessFilterHelper$AccessChecker.<init>:void()`  (from `internal/ReflectionAccessFilterHelper.java`) -/
def f_com_google_gson_internal_ReflectionAccessFilterHelper_AccessChecker__init__void__ : Func :=
  { name := "com.google.gson.internal.ReflectionAccessFilterHelper$AccessChecker.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.Streams.<init>:void()`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams__init__void__ : Func :=
  { name := "com.google.gson.internal.Streams.<init>:void()"
  , params := ["this"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.Streams.parse:com.google.gson.JsonElement(com.google.gson.stream.JsonReader)`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_parse_com_google_gson_JsonElement_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.Streams.parse:com.google.gson.JsonElement(com.google.gson.stream.JsonReader)"
  , params := ["reader"]
  , body := (.seq
            .skip
            (.seq (.assign "isEmpty" (.lit (.bool true))) (.hole "control:TRY-multiCatch"))) }

/-- `com.google.gson.internal.Streams.write:void(com.google.gson.JsonElement,com.google.gson.stream.JsonWriter)`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_write_void_com_google_gson_JsonElement_com_google_gson_stream_JsonWriter_ : Func :=
  { name := "com.google.gson.internal.Streams.write:void(com.google.gson.JsonElement,com.google.gson.stream.JsonWriter)"
  , params := ["element", "writer"]
  , body := (.expr
            (.mcall
              (.name "JsonElementTypeAdapter")
              "ADAPTER"
              [(.name "writer"), (.name "element")])) }

/-- `com.google.gson.internal.Streams.writerForAppendable:java.io.Writer(java.lang.Appendable)`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_writerForAppendable_java_io_Writer_java_lang_Appendable_ : Func :=
  { name := "com.google.gson.internal.Streams.writerForAppendable:java.io.Writer(java.lang.Appendable)"
  , params := ["appendable"]
  , body := (.ret (.cond (.hole "op:instanceOf") (.hole "op:cast") (.hole "expr:BLOCK-impure"))) }

/-- `com.google.gson.internal.Streams$AppendableWriter.<init>:void(java.lang.Appendable)`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter__init__void_java_lang_Appendable_ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter.<init>:void(java.lang.Appendable)"
  , params := ["this", "appendable"]
  , body := (.seq
            (.setField (.name "this") "currentWrite" (.hole "op:alloc"))
            (.seq
              (.expr (.mcall (.name "this") "currentWrite" [(.name "this")]))
              (.setField (.name "this") "appendable" (.name "appendable")))) }

/-- `com.google.gson.internal.Streams$AppendableWriter.write:void(char[],int,int)`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter_write_void_char___int_int_ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter.write:void(char[],int,int)"
  , params := ["this", "chars", "offset", "length"]
  , body := (.seq
            (.expr (.mcall (.name "this") "currentWrite" [(.name "chars")]))
            (.expr
              (.mcall
                (.name "this")
                "appendable"
                [ (.field (.name "this") "currentWrite")
                , (.name "offset")
                , (.binop "+" (.name "offset") (.name "length")) ]))) }

/-- `com.google.gson.internal.Streams$AppendableWriter.flush:void()`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter_flush_void__ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter.flush:void()"
  , params := ["this"]
  , body := (.ifte (.hole "op:instanceOf") (.expr (.call "flush" [])) .skip) }

/-- `com.google.gson.internal.Streams$AppendableWriter.close:void()`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter_close_void__ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter.close:void()"
  , params := ["this"]
  , body := (.ifte (.hole "op:instanceOf") (.expr (.call "close" [])) .skip) }

/-- `com.google.gson.internal.Streams$AppendableWriter.write:void(int)`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter_write_void_int_ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter.write:void(int)"
  , params := ["this", "i"]
  , body := (.expr (.mcall (.name "this") "appendable" [(.hole "op:cast")])) }

/-- `com.google.gson.internal.Streams$AppendableWriter.write:void(java.lang.String,int,int)`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter_write_void_java_lang_String_int_int_ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter.write:void(java.lang.String,int,int)"
  , params := ["this", "str", "off", "len"]
  , body := (.seq
            (.expr (.call "requireNonNull" [(.name "str")]))
            (.expr
              (.mcall
                (.name "this")
                "appendable"
                [(.name "str"), (.name "off"), (.binop "+" (.name "off") (.name "len"))]))) }

/-- `com.google.gson.internal.Streams$AppendableWriter.append:java.io.Writer(java.lang.CharSequence)`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter_append_java_io_Writer_java_lang_CharSequence_ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter.append:java.io.Writer(java.lang.CharSequence)"
  , params := ["this", "csq"]
  , body := (.seq (.expr (.mcall (.name "this") "appendable" [(.name "csq")])) (.ret (.name "this"))) }

/-- `com.google.gson.internal.Streams$AppendableWriter.append:java.io.Writer(java.lang.CharSequence,int,int)`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter_append_java_io_Writer_java_lang_CharSequence_int_int_ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter.append:java.io.Writer(java.lang.CharSequence,int,int)"
  , params := ["this", "csq", "start", "end"]
  , body := (.seq
            (.expr
              (.mcall (.name "this") "appendable" [(.name "csq"), (.name "start"), (.name "end")]))
            (.ret (.name "this"))) }

/-- `com.google.gson.internal.Streams$AppendableWriter$CurrentWrite.setChars:void(char[])`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter_CurrentWrite_setChars_void_char___ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter$CurrentWrite.setChars:void(char[])"
  , params := ["this", "chars"]
  , body := (.seq
            (.setField (.name "this") "chars" (.name "chars"))
            (.setField (.name "this") "cachedString" (.lit .unit))) }

/-- `com.google.gson.internal.Streams$AppendableWriter$CurrentWrite.length:int()`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter_CurrentWrite_length_int__ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter$CurrentWrite.length:int()"
  , params := ["this"]
  , body := (.ret (.hole "op:sizeOf")) }

/-- `com.google.gson.internal.Streams$AppendableWriter$CurrentWrite.charAt:char(int)`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter_CurrentWrite_charAt_char_int_ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter$CurrentWrite.charAt:char(int)"
  , params := ["this", "i"]
  , body := (.ret (.index (.field (.name "this") "chars") (.name "i"))) }

/-- `com.google.gson.internal.Streams$AppendableWriter$CurrentWrite.subSequence:java.lang.CharSequence(int,int)`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter_CurrentWrite_subSequence_java_lang_CharSequence_int_int_ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter$CurrentWrite.subSequence:java.lang.CharSequence(int,int)"
  , params := ["this", "start", "end"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj5" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "<init>"
                    [ (.field (.name "this") "chars")
                    , (.name "start")
                    , (.binop "-" (.name "end") (.name "start")) ]))
                (.ret (.name "$obj5"))))) }

/-- `com.google.gson.internal.Streams$AppendableWriter$CurrentWrite.toString:java.lang.String()`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter_CurrentWrite_toString_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter$CurrentWrite.toString:java.lang.String()"
  , params := ["this"]
  , body := (.seq
            (.ifte
              (.binop "==" (.field (.name "this") "cachedString") (.lit .unit))
              (.seq
                (.setField (.name "this") "cachedString" (.hole "op:alloc"))
                (.expr (.mcall (.name "this") "cachedString" [(.field (.name "this") "chars")])))
              .skip)
            (.ret (.field (.name "this") "cachedString"))) }

/-- `com.google.gson.internal.Streams$AppendableWriter$CurrentWrite.<init>:void()`  (from `internal/Streams.java`) -/
def f_com_google_gson_internal_Streams_AppendableWriter_CurrentWrite__init__void__ : Func :=
  { name := "com.google.gson.internal.Streams$AppendableWriter$CurrentWrite.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.TroubleshootingGuide.<init>:void()`  (from `internal/TroubleshootingGuide.java`) -/
def f_com_google_gson_internal_TroubleshootingGuide__init__void__ : Func :=
  { name := "com.google.gson.internal.TroubleshootingGuide.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.TroubleshootingGuide.createUrl:java.lang.String(java.lang.String)`  (from `internal/TroubleshootingGuide.java`) -/
def f_com_google_gson_internal_TroubleshootingGuide_createUrl_java_lang_String_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.TroubleshootingGuide.createUrl:java.lang.String(java.lang.String)"
  , params := ["id"]
  , body := (.ret
            (.binop
              "+"
              (.lit (.str "https://github.com/google/gson/blob/main/Troubleshooting.md#"))
              (.name "id"))) }

/-- `com.google.gson.internal.UnsafeAllocator.newInstance:java.lang.Object(java.lang.Class)`  (from `internal/UnsafeAllocator.java`) -/
def f_com_google_gson_internal_UnsafeAllocator_newInstance_java_lang_Object_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.UnsafeAllocator.newInstance:java.lang.Object(java.lang.Class)"
  , params := ["this", "c"]
  , body := .skip }

/-- `com.google.gson.internal.UnsafeAllocator.assertInstantiable:void(java.lang.Class)`  (from `internal/UnsafeAllocator.java`) -/
def f_com_google_gson_internal_UnsafeAllocator_assertInstantiable_void_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.UnsafeAllocator.assertInstantiable:void(java.lang.Class)"
  , params := ["c"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "exceptionMessage"
                (.call
                  "com.google.gson.internal.ConstructorConstructor.checkInstantiable:java.lang.String(java.lang.Class)"
                  [(.name "c")]))
              (.ifte
                (.binop "!=" (.name "exceptionMessage") (.lit .unit))
                (.hole "control:THROW")
                .skip))) }

/-- `com.google.gson.internal.UnsafeAllocator.create:com.google.gson.internal.UnsafeAllocator()`  (from `internal/UnsafeAllocator.java`) -/
def f_com_google_gson_internal_UnsafeAllocator_create_com_google_gson_internal_UnsafeAllocator__ : Func :=
  { name := "com.google.gson.internal.UnsafeAllocator.create:com.google.gson.internal.UnsafeAllocator()"
  , params := []
  , body := (.seq
            (.tryCatch
              (.seq
                .skip
                (.seq
                  (.assign "unsafeClass" (.call "forName" [(.lit (.str "sun.misc.Unsafe"))]))
                  (.seq
                    .skip
                    (.seq
                      (.assign "f" (.call "getDeclaredField" [(.lit (.str "theUnsafe"))]))
                      (.seq
                        (.expr (.call "setAccessible" [(.lit (.bool true))]))
                        (.seq
                          .skip
                          (.seq
                            (.assign "unsafe" (.call "get" [(.lit .unit)]))
                            (.seq
                              .skip
                              (.seq
                                (.assign
                                  "allocateInstance"
                                  (.call
                                    "getMethod"
                                    [ (.lit (.str "allocateInstance"))
                                    , (.hole "op:arrayInitializer") ]))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "$obj1" (.hole "op:alloc"))
                                    (.seq
                                      (.expr
                                        (.call
                                        "com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$0.<init>:void()"
                                        [(.name "allocateInstance"), (.name "unsafe")]))
                                      (.ret (.name "$obj1"))))))))))))))
              "__exc"
              .skip)
            (.seq
              (.tryCatch
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "getConstructorId"
                      (.mcall
                        (.name "ObjectStreamClass")
                        "class"
                        [(.lit (.str "getConstructorId")), (.hole "op:arrayInitializer")]))
                    (.seq
                      (.expr (.call "setAccessible" [(.lit (.bool true))]))
                      (.seq
                        .skip
                        (.seq
                          (.assign "constructorId" (.hole "op:cast"))
                          (.seq
                            .skip
                            (.seq
                              (.assign
                                "newInstance"
                                (.mcall
                                  (.name "ObjectStreamClass")
                                  "class"
                                  [(.lit (.str "newInstance")), (.hole "op:arrayInitializer")]))
                              (.seq
                                (.expr (.call "setAccessible" [(.lit (.bool true))]))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "$obj2" (.hole "op:alloc"))
                                    (.seq
                                      (.expr
                                        (.call
                                        "com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$1.<init>:void()"
                                        [(.name "constructorId"), (.name "newInstance")]))
                                      (.ret (.name "$obj2")))))))))))))
                "__exc"
                .skip)
              (.seq
                (.tryCatch
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "newInstance"
                        (.mcall
                          (.name "ObjectInputStream")
                          "class"
                          [(.lit (.str "newInstance")), (.hole "op:arrayInitializer")]))
                      (.seq
                        (.expr (.call "setAccessible" [(.lit (.bool true))]))
                        (.seq
                          .skip
                          (.seq
                            (.assign "$obj3" (.hole "op:alloc"))
                            (.seq
                              (.expr
                                (.call
                                  "com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$2.<init>:void()"
                                  [(.name "newInstance")]))
                              (.ret (.name "$obj3"))))))))
                  "__exc"
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "$obj4" (.hole "op:alloc"))
                    (.seq
                      (.expr
                        (.call
                          "com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$3.<init>:void()"
                          []))
                      (.ret (.name "$obj4")))))))) }

/-- `com.google.gson.internal.UnsafeAllocator.<init>:void()`  (from `internal/UnsafeAllocator.java`) -/
def f_com_google_gson_internal_UnsafeAllocator__init__void__ : Func :=
  { name := "com.google.gson.internal.UnsafeAllocator.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.UnsafeAllocator.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_UnsafeAllocator__clinit__void__ : Func :=
  { name := "com.google.gson.internal.UnsafeAllocator.<clinit>:void()"
  , params := []
  , body := (.setField
            (.fnref "com.google.gson.internal.UnsafeAllocator")
            "INSTANCE"
            (.call
              "com.google.gson.internal.UnsafeAllocator.create:com.google.gson.internal.UnsafeAllocator()"
              [])) }

/-- `com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$0.newInstance:java.lang.Object(java.lang.Class)`  (from `internal/UnsafeAllocator.java`) -/
def f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_0_newInstance_java_lang_Object_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$0.newInstance:java.lang.Object(java.lang.Class)"
  , params := ["this", "c"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.UnsafeAllocator.assertInstantiable:void(java.lang.Class)"
                [(.name "c")]))
            (.ret (.hole "op:cast"))) }

/-- `com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$0.<init>:void()`  (from `internal/UnsafeAllocator.java`) -/
def f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_0__init__void__ : Func :=
  { name := "com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$0.<init>:void()"
  , params := ["this", "allocateInstance", "unsafe"]
  , body := (.seq
            (.setField (.name "this") "allocateInstance" (.name "allocateInstance"))
            (.setField (.name "this") "unsafe" (.name "unsafe"))) }

/-- `com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$1.newInstance:java.lang.Object(java.lang.Class)`  (from `internal/UnsafeAllocator.java`) -/
def f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_1_newInstance_java_lang_Object_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$1.newInstance:java.lang.Object(java.lang.Class)"
  , params := ["this", "c"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.UnsafeAllocator.assertInstantiable:void(java.lang.Class)"
                [(.name "c")]))
            (.ret (.hole "op:cast"))) }

/-- `com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$1.<init>:void()`  (from `internal/UnsafeAllocator.java`) -/
def f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_1__init__void__ : Func :=
  { name := "com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$1.<init>:void()"
  , params := ["this", "constructorId", "newInstance"]
  , body := (.seq
            (.setField (.name "this") "constructorId" (.name "constructorId"))
            (.setField (.name "this") "newInstance" (.name "newInstance"))) }

/-- `com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$2.newInstance:java.lang.Object(java.lang.Class)`  (from `internal/UnsafeAllocator.java`) -/
def f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_2_newInstance_java_lang_Object_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$2.newInstance:java.lang.Object(java.lang.Class)"
  , params := ["this", "c"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.UnsafeAllocator.assertInstantiable:void(java.lang.Class)"
                [(.name "c")]))
            (.ret (.hole "op:cast"))) }

/-- `com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$2.<init>:void()`  (from `internal/UnsafeAllocator.java`) -/
def f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_2__init__void__ : Func :=
  { name := "com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$2.<init>:void()"
  , params := ["this", "newInstance"]
  , body := (.setField (.name "this") "newInstance" (.name "newInstance")) }

/-- `com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$3.newInstance:java.lang.Object(java.lang.Class)`  (from `internal/UnsafeAllocator.java`) -/
def f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_3_newInstance_java_lang_Object_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$3.newInstance:java.lang.Object(java.lang.Class)"
  , params := ["this", "c"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$3.<init>:void()`  (from `internal/UnsafeAllocator.java`) -/
def f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_3__init__void__ : Func :=
  { name := "com.google.gson.internal.UnsafeAllocator.create.UnsafeAllocator$3.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.ArrayTypeAdapter.<init>:void(com.google.gson.Gson,com.google.gson.TypeAdapter,java.lang.Class)`  (from `internal/bind/ArrayTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ArrayTypeAdapter__init__void_com_google_gson_Gson_com_google_gson_TypeAdapter_java_lang_ : Func :=
  { name := "com.google.gson.internal.bind.ArrayTypeAdapter.<init>:void(com.google.gson.Gson,com.google.gson.TypeAdapter,java.lang.Class)"
  , params := ["this", "context", "componentTypeAdapter", "componentType"]
  , body := (.seq
            (.setField (.name "this") "componentTypeAdapter" (.hole "op:alloc"))
            (.seq
              (.expr
                (.mcall
                  (.name "this")
                  "componentTypeAdapter"
                  [(.name "context"), (.name "componentTypeAdapter"), (.name "componentType")]))
              (.setField (.name "this") "componentType" (.name "componentType")))) }

/-- `com.google.gson.internal.bind.ArrayTypeAdapter.read:java.lang.Object(com.google.gson.stream.JsonReader)`  (from `internal/bind/ArrayTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ArrayTypeAdapter_read_java_lang_Object_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.bind.ArrayTypeAdapter.read:java.lang.Object(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "list" (.hole "op:alloc"))
                (.seq
                  (.expr (.call "<init>" []))
                  (.seq
                    (.expr (.call "beginArray" []))
                    (.seq
                      (.loop
                        (.call "hasNext" [])
                        (.seq
                          .skip
                          (.seq
                            (.assign
                              "instance"
                              (.mcall (.name "this") "componentTypeAdapter" [(.name "in")]))
                            (.expr (.call "add" [(.name "instance")])))))
                      (.seq
                        (.expr (.call "endArray" []))
                        (.seq
                          .skip
                          (.seq
                            (.assign "size" (.call "size" []))
                            (.ifte
                              (.mcall (.name "this") "componentType" [])
                              (.seq
                                .skip
                                (.seq
                                  (.assign
                                    "array"
                                    (.call
                                      "newInstance"
                                      [(.field (.name "this") "componentType"), (.name "size")]))
                                  (.seq (.hole "control:FOR") (.ret (.name "array")))))
                              (.seq
                                .skip
                                (.seq
                                  (.assign "array" (.hole "op:cast"))
                                  (.ret (.call "toArray" [(.name "array")])))))))))))))) }

/-- `com.google.gson.internal.bind.ArrayTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)`  (from `internal/bind/ArrayTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ArrayTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.bind.ArrayTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)"
  , params := ["this", "out", "array"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "array") (.lit .unit))
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              (.expr (.call "beginArray" []))
              (.seq (.hole "control:FOR") (.expr (.call "endArray" []))))) }

/-- `com.google.gson.internal.bind.ArrayTypeAdapter.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_ArrayTypeAdapter__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.ArrayTypeAdapter.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.bind.ArrayTypeAdapter")
              "FACTORY"
              (.hole "op:alloc"))
            (.expr (.mcall (.fnref "com.google.gson.internal.bind.ArrayTypeAdapter") "FACTORY" []))) }

/-- `com.google.gson.internal.bind.ArrayTypeAdapter.FACTORY.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/ArrayTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ArrayTypeAdapter_FACTORY_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_goo : Func :=
  { name := "com.google.gson.internal.bind.ArrayTypeAdapter.FACTORY.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.seq
            .skip
            (.seq
              (.assign "type" (.call "getType" []))
              (.seq
                (.ifte
                  (.unop
                    "!"
                    (.binop
                      "||"
                      (.hole "op:instanceOf")
                      (.binop "&&" (.hole "op:instanceOf") (.call "isArray" []))))
                  (.ret (.lit .unit))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "componentType"
                      (.call
                        "com.google.gson.internal.GsonTypes.getArrayComponentType:java.lang.reflect.Type(java.lang.reflect.Type)"
                        [(.name "type")]))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "componentTypeAdapter"
                          (.call "getAdapter" [(.call "get" [(.name "componentType")])]))
                        (.seq
                          .skip
                          (.seq
                            (.assign "arrayAdapter" (.hole "op:alloc"))
                            (.seq
                              (.expr
                                (.call
                                  "<init>"
                                  [ (.name "gson")
                                  , (.name "componentTypeAdapter")
                                  , (.call
                                      "com.google.gson.internal.GsonTypes.getRawType:java.lang.Class(java.lang.reflect.Type)"
                                      [(.name "componentType")]) ]))
                              (.ret (.name "arrayAdapter")))))))))))) }

/-- `com.google.gson.internal.bind.ArrayTypeAdapter.FACTORY.TypeAdapterFactory$0.<init>:void()`  (from `internal/bind/ArrayTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ArrayTypeAdapter_FACTORY_TypeAdapterFactory_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.ArrayTypeAdapter.FACTORY.TypeAdapterFactory$0.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.CollectionTypeAdapterFactory.<init>:void(com.google.gson.internal.ConstructorConstructor)`  (from `internal/bind/CollectionTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_CollectionTypeAdapterFactory__init__void_com_google_gson_internal_ConstructorConstructor : Func :=
  { name := "com.google.gson.internal.bind.CollectionTypeAdapterFactory.<init>:void(com.google.gson.internal.ConstructorConstructor)"
  , params := ["this", "constructorConstructor"]
  , body := (.setField (.name "this") "constructorConstructor" (.name "constructorConstructor")) }

/-- `com.google.gson.internal.bind.CollectionTypeAdapterFactory.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/CollectionTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_CollectionTypeAdapterFactory_create_com_google_gson_TypeAdapter_com_google_gson_Gson_com : Func :=
  { name := "com.google.gson.internal.bind.CollectionTypeAdapterFactory.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.seq
            .skip
            (.seq
              (.assign "type" (.call "getType" []))
              (.seq
                .skip
                (.seq
                  (.assign "rawType" (.call "getRawType" []))
                  (.seq
                    (.ifte
                      (.unop "!" (.mcall (.name "Collection") "class" [(.name "rawType")]))
                      (.ret (.lit .unit))
                      .skip)
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "elementType"
                          (.call
                            "com.google.gson.internal.GsonTypes.getCollectionElementType:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class)"
                            [(.name "type"), (.name "rawType")]))
                        (.seq
                          .skip
                          (.seq
                            (.assign
                              "elementTypeAdapter"
                              (.call "getAdapter" [(.call "get" [(.name "elementType")])]))
                            (.seq
                              .skip
                              (.seq
                                (.assign "wrappedTypeAdapter" (.hole "op:alloc"))
                                (.seq
                                  (.expr
                                    (.call
                                      "<init>"
                                      [ (.name "gson")
                                      , (.name "elementTypeAdapter")
                                      , (.name "elementType") ]))
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign "allowUnsafe" (.lit (.bool false)))
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "constructor"
                                        (.mcall
                                        (.name "this")
                                        "constructorConstructor"
                                        [(.name "typeToken"), (.name "allowUnsafe")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "result" (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "<init>"
                                        [(.name "wrappedTypeAdapter"), (.name "constructor")]))
                                        (.ret (.name "result"))))))))))))))))))))) }

/-- `com.google.gson.internal.bind.CollectionTypeAdapterFactory$Adapter.<init>:void(com.google.gson.TypeAdapter,com.google.gson.internal.ObjectConstructor)`  (from `internal/bind/CollectionTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_CollectionTypeAdapterFactory_Adapter__init__void_com_google_gson_TypeAdapter_com_google_ : Func :=
  { name := "com.google.gson.internal.bind.CollectionTypeAdapterFactory$Adapter.<init>:void(com.google.gson.TypeAdapter,com.google.gson.internal.ObjectConstructor)"
  , params := ["this", "elementTypeAdapter", "constructor"]
  , body := (.seq
            (.setField (.name "this") "elementTypeAdapter" (.name "elementTypeAdapter"))
            (.setField (.name "this") "constructor" (.name "constructor"))) }

/-- `com.google.gson.internal.bind.CollectionTypeAdapterFactory$Adapter.read:java.util.Collection(com.google.gson.stream.JsonReader)`  (from `internal/bind/CollectionTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_CollectionTypeAdapterFactory_Adapter_read_java_util_Collection_com_google_gson_stream_Js : Func :=
  { name := "com.google.gson.internal.bind.CollectionTypeAdapterFactory$Adapter.read:java.util.Collection(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "collection" (.mcall (.name "this") "constructor" []))
                (.seq
                  (.expr (.call "beginArray" []))
                  (.seq
                    (.loop
                      (.call "hasNext" [])
                      (.seq
                        .skip
                        (.seq
                          (.assign
                            "instance"
                            (.mcall (.name "this") "elementTypeAdapter" [(.name "in")]))
                          (.expr (.call "add" [(.name "instance")])))))
                    (.seq (.expr (.call "endArray" [])) (.ret (.name "collection")))))))) }

/-- `com.google.gson.internal.bind.CollectionTypeAdapterFactory$Adapter.write:void(com.google.gson.stream.JsonWriter,java.util.Collection)`  (from `internal/bind/CollectionTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_CollectionTypeAdapterFactory_Adapter_write_void_com_google_gson_stream_JsonWriter_java_u : Func :=
  { name := "com.google.gson.internal.bind.CollectionTypeAdapterFactory$Adapter.write:void(com.google.gson.stream.JsonWriter,java.util.Collection)"
  , params := ["this", "out", "collection"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "collection") (.lit .unit))
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              (.expr (.call "beginArray" []))
              (.seq
                .skip
                (.seq
                  (.assign "$iterLocal0" (.call "iterator" []))
                  (.seq
                    (.loop
                      (.call "hasNext" [])
                      (.seq
                        .skip
                        (.seq
                          (.assign "element" (.call "next" []))
                          (.expr
                            (.mcall
                              (.name "this")
                              "elementTypeAdapter"
                              [(.name "out"), (.name "element")])))))
                    (.expr (.call "endArray" []))))))) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.<init>:void(java.lang.Class)`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType__init__void_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.<init>:void(java.lang.Class)"
  , params := ["this", "dateClass"]
  , body := (.setField (.name "this") "dateClass" (.name "dateClass")) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.deserialize:java.util.Date(java.util.Date)`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType_deserialize_java_util_Date_java_util_Date_ : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.deserialize:java.util.Date(java.util.Date)"
  , params := ["this", "date"]
  , body := .skip }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.createFactory:com.google.gson.TypeAdapterFactory(com.google.gson.internal.bind.DefaultDateTypeAdapter)`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType_createFactory_com_google_gson_TypeAdapterFactory_com_goo : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.createFactory:com.google.gson.TypeAdapterFactory(com.google.gson.internal.bind.DefaultDateTypeAdapter)"
  , params := ["this", "adapter"]
  , body := (.ret (.call "newFactory" [(.field (.name "this") "dateClass"), (.name "adapter")])) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.createAdapterFactory:com.google.gson.TypeAdapterFactory(java.lang.String)`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType_createAdapterFactory_com_google_gson_TypeAdapterFactory_ : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.createAdapterFactory:com.google.gson.TypeAdapterFactory(java.lang.String)"
  , params := ["this", "datePattern"]
  , body := (.ret
            (.call
              "com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.createFactory:com.google.gson.TypeAdapterFactory(com.google.gson.internal.bind.DefaultDateTypeAdapter)"
              [(.hole "expr:BLOCK-impure")])) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.createAdapterFactory:com.google.gson.TypeAdapterFactory(int,int)`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType_createAdapterFactory_com_google_gson_TypeAdapterFactory_' : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.createAdapterFactory:com.google.gson.TypeAdapterFactory(int,int)"
  , params := ["this", "dateStyle", "timeStyle"]
  , body := (.ret
            (.call
              "com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.createFactory:com.google.gson.TypeAdapterFactory(com.google.gson.internal.bind.DefaultDateTypeAdapter)"
              [(.hole "expr:BLOCK-impure")])) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType")
              "DATE"
              (.hole "op:alloc"))
            (.expr
              (.mcall
                (.fnref "com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType")
                "DATE"
                [(.field (.name "Date") "class")]))) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.DATE.DateType$0.deserialize:java.util.Date(java.util.Date)`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType_DATE_DateType_0_deserialize_java_util_Date_java_util_Dat : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.DATE.DateType$0.deserialize:java.util.Date(java.util.Date)"
  , params := ["this", "date"]
  , body := (.ret (.name "date")) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.DATE.DateType$0.<init>:void()`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType_DATE_DateType_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType.DATE.DateType$0.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter.<init>:void(com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType,java.lang.String)`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter__init__void_com_google_gson_internal_bind_DefaultDateTypeAdapter_ : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter.<init>:void(com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType,java.lang.String)"
  , params := ["this", "dateType", "datePattern"]
  , body := (.seq
            (.setField (.name "this") "dateFormats" (.hole "op:alloc"))
            (.seq
              (.expr (.mcall (.name "this") "dateFormats" []))
              (.seq
                (.setField (.name "this") "dateType" (.call "requireNonNull" [(.name "dateType")]))
                (.seq
                  (.expr (.mcall (.name "this") "dateFormats" [(.hole "expr:BLOCK-impure")]))
                  (.ifte
                    (.unop "!" (.call "equals" [(.field (.name "Locale") "US")]))
                    (.expr (.mcall (.name "this") "dateFormats" [(.hole "expr:BLOCK-impure")]))
                    .skip))))) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter.<init>:void(com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType,int,int)`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter__init__void_com_google_gson_internal_bind_DefaultDateTypeAdapter_' : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter.<init>:void(com.google.gson.internal.bind.DefaultDateTypeAdapter$DateType,int,int)"
  , params := ["this", "dateType", "dateStyle", "timeStyle"]
  , body := (.seq
            (.setField (.name "this") "dateFormats" (.hole "op:alloc"))
            (.seq
              (.expr (.mcall (.name "this") "dateFormats" []))
              (.seq
                (.setField (.name "this") "dateType" (.call "requireNonNull" [(.name "dateType")]))
                (.seq
                  (.expr
                    (.mcall
                      (.name "this")
                      "dateFormats"
                      [ (.call
                          "getDateTimeInstance"
                          [(.name "dateStyle"), (.name "timeStyle"), (.field (.name "Locale") "US")]) ]))
                  (.seq
                    (.ifte
                      (.unop "!" (.call "equals" [(.field (.name "Locale") "US")]))
                      (.expr
                        (.mcall
                          (.name "this")
                          "dateFormats"
                          [(.call "getDateTimeInstance" [(.name "dateStyle"), (.name "timeStyle")])]))
                      .skip)
                    (.ifte
                      (.call "com.google.gson.internal.JavaVersion.isJava9OrLater:boolean()" [])
                      (.expr
                        (.mcall
                          (.name "this")
                          "dateFormats"
                          [ (.call
                              "com.google.gson.internal.PreJava9DateFormatProvider.getUsDateTimeFormat:java.text.DateFormat(int,int)"
                              [(.name "dateStyle"), (.name "timeStyle")]) ]))
                      .skip)))))) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.util.Date)`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_util_Date_ : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.util.Date)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "value") (.lit .unit))
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "dateFormat" (.mcall (.name "this") "dateFormats" [(.lit (.int 0))]))
                (.seq
                  .skip
                  (.seq
                    (.seq
                      (.hole "stmt:MODIFIER")
                      (.seq
                        (.expr (.field (.name "this") "dateFormats"))
                        (.assign "dateFormatAsString" (.call "format" [(.name "value")]))))
                    (.expr (.call "value" [(.name "dateFormatAsString")]))))))) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter.read:java.util.Date(com.google.gson.stream.JsonReader)`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_read_java_util_Date_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter.read:java.util.Date(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign
                  "date"
                  (.call
                    "com.google.gson.internal.bind.DefaultDateTypeAdapter.deserializeToDate:java.util.Date(com.google.gson.stream.JsonReader)"
                    [(.name "in")]))
                (.ret (.mcall (.name "this") "dateType" [(.name "date")]))))) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter.deserializeToDate:java.util.Date(com.google.gson.stream.JsonReader)`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_deserializeToDate_java_util_Date_com_google_gson_stream_JsonReade : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter.deserializeToDate:java.util.Date(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              (.assign "s" (.call "nextString" []))
              (.seq
                (.seq
                  (.hole "stmt:MODIFIER")
                  (.seq
                    (.expr (.field (.name "this") "dateFormats"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "$iterLocal0" (.mcall (.name "this") "dateFormats" []))
                        (.loop
                          (.call "hasNext" [])
                          (.seq
                            .skip
                            (.seq
                              (.assign "dateFormat" (.call "next" []))
                              (.seq
                                .skip
                                (.seq
                                  (.assign "originalTimeZone" (.call "getTimeZone" []))
                                  (.tryFinally
                                    (.tryCatch (.ret (.call "parse" [(.name "s")])) "__exc" .skip)
                                    (.expr (.call "setTimeZone" [(.name "originalTimeZone")]))))))))))))
                (.tryCatch
                  (.ret
                    (.call
                      "com.google.gson.internal.bind.util.ISO8601Utils.parse:java.util.Date(java.lang.String,java.text.ParsePosition)"
                      [(.name "s"), (.hole "expr:BLOCK-impure")]))
                  "__exc"
                  (.hole "control:THROW"))))) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter.toString:java.lang.String()`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_toString_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter.toString:java.lang.String()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "defaultFormat" (.mcall (.name "this") "dateFormats" [(.lit (.int 0))]))
              (.ifte
                (.hole "op:instanceOf")
                (.ret
                  (.binop
                    "+"
                    (.binop
                      "+"
                      (.binop
                        "+"
                        (.field
                          (.fnref "com.google.gson.internal.bind.DefaultDateTypeAdapter")
                          "SIMPLE_NAME")
                        (.lit (.str "(")))
                      (.call "toPattern" []))
                    (.lit (.str ")"))))
                (.ret
                  (.binop
                    "+"
                    (.binop
                      "+"
                      (.binop
                        "+"
                        (.field
                          (.fnref "com.google.gson.internal.bind.DefaultDateTypeAdapter")
                          "SIMPLE_NAME")
                        (.lit (.str "(")))
                      (.call "getSimpleName" []))
                    (.lit (.str ")"))))))) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.bind.DefaultDateTypeAdapter")
              "SIMPLE_NAME"
              (.lit (.str "DefaultDateTypeAdapter")))
            (.seq
              (.setField
                (.fnref "com.google.gson.internal.bind.DefaultDateTypeAdapter")
                "DEFAULT_STYLE_FACTORY"
                (.hole "op:alloc"))
              (.expr
                (.mcall
                  (.fnref "com.google.gson.internal.bind.DefaultDateTypeAdapter")
                  "DEFAULT_STYLE_FACTORY"
                  [])))) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter.DEFAULT_STYLE_FACTORY.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DEFAULT_STYLE_FACTORY_TypeAdapterFactory_0_create_com_google_gson : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter.DEFAULT_STYLE_FACTORY.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.ret
            (.cond
              (.binop "==" (.call "getRawType" []) (.field (.name "Date") "class"))
              (.hole "op:cast")
              (.lit .unit))) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter.DEFAULT_STYLE_FACTORY.TypeAdapterFactory$0.toString:<unresolvedSignature>(0)`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DEFAULT_STYLE_FACTORY_TypeAdapterFactory_0_toString__unresolvedSi : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter.DEFAULT_STYLE_FACTORY.TypeAdapterFactory$0.toString:<unresolvedSignature>(0)"
  , params := ["this"]
  , body := (.ret (.lit (.str "DefaultDateTypeAdapter#DEFAULT_STYLE_FACTORY"))) }

/-- `com.google.gson.internal.bind.DefaultDateTypeAdapter.DEFAULT_STYLE_FACTORY.TypeAdapterFactory$0.<init>:void()`  (from `internal/bind/DefaultDateTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DEFAULT_STYLE_FACTORY_TypeAdapterFactory_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.DefaultDateTypeAdapter.DEFAULT_STYLE_FACTORY.TypeAdapterFactory$0.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.EnumTypeAdapter.calculateHashMapCapacity:int(int)`  (from `internal/bind/EnumTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_EnumTypeAdapter_calculateHashMapCapacity_int_int_ : Func :=
  { name := "com.google.gson.internal.bind.EnumTypeAdapter.calculateHashMapCapacity:int(int)"
  , params := ["numMappings"]
  , body := (.ret (.hole "op:cast")) }

/-- `com.google.gson.internal.bind.EnumTypeAdapter.<init>:void(java.lang.Class)`  (from `internal/bind/EnumTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_EnumTypeAdapter__init__void_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.bind.EnumTypeAdapter.<init>:void(java.lang.Class)"
  , params := ["this", "classOfT"]
  , body := (.tryCatch
            (.seq
              .skip
              (.seq
                (.assign "fields" (.call "getDeclaredFields" []))
                (.seq
                  .skip
                  (.seq
                    (.assign "constantCount" (.lit (.int 0)))
                    (.seq
                      (.hole "control:FOR")
                      (.seq
                        (.assign
                          "fields"
                          (.call "copyOf" [(.name "fields"), (.name "constantCount")]))
                        (.seq
                          .skip
                          (.seq
                            (.assign
                              "hashMapCapacity"
                              (.call
                                "com.google.gson.internal.bind.EnumTypeAdapter.calculateHashMapCapacity:int(int)"
                                [(.name "constantCount")]))
                            (.seq
                              (.setField (.name "this") "nameToConstant" (.hole "op:alloc"))
                              (.seq
                                (.expr
                                  (.mcall
                                    (.name "this")
                                    "nameToConstant"
                                    [(.name "hashMapCapacity")]))
                                (.seq
                                  (.setField (.name "this") "stringToConstant" (.hole "op:alloc"))
                                  (.seq
                                    (.expr
                                      (.mcall
                                        (.name "this")
                                        "stringToConstant"
                                        [(.name "hashMapCapacity")]))
                                    (.seq
                                      (.setField (.name "this") "constantToName" (.hole "op:alloc"))
                                      (.seq
                                        (.expr
                                        (.mcall
                                        (.name "this")
                                        "constantToName"
                                        [(.name "hashMapCapacity")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "setAccessible"
                                        [(.name "fields"), (.lit (.bool true))]))
                                        (.hole "control:FOR"))))))))))))))))
            "__exc"
            (.hole "control:THROW")) }

/-- `com.google.gson.internal.bind.EnumTypeAdapter.read:java.lang.Enum(com.google.gson.stream.JsonReader)`  (from `internal/bind/EnumTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_EnumTypeAdapter_read_java_lang_Enum_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.bind.EnumTypeAdapter.read:java.lang.Enum(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "key" (.call "nextString" []))
                (.seq
                  .skip
                  (.seq
                    (.assign "constant" (.mcall (.name "this") "nameToConstant" [(.name "key")]))
                    (.ret
                      (.cond
                        (.binop "==" (.name "constant") (.lit .unit))
                        (.mcall (.name "this") "stringToConstant" [(.name "key")])
                        (.name "constant")))))))) }

/-- `com.google.gson.internal.bind.EnumTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Enum)`  (from `internal/bind/EnumTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_EnumTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Enum_ : Func :=
  { name := "com.google.gson.internal.bind.EnumTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Enum)"
  , params := ["this", "out", "value"]
  , body := (.expr
            (.call
              "value"
              [ (.cond
                  (.binop "==" (.name "value") (.lit .unit))
                  (.lit .unit)
                  (.mcall (.name "this") "constantToName" [(.name "value")])) ])) }

/-- `com.google.gson.internal.bind.EnumTypeAdapter.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_EnumTypeAdapter__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.EnumTypeAdapter.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.bind.EnumTypeAdapter")
              "FACTORY"
              (.hole "op:alloc"))
            (.expr (.mcall (.fnref "com.google.gson.internal.bind.EnumTypeAdapter") "FACTORY" []))) }

/-- `com.google.gson.internal.bind.EnumTypeAdapter.FACTORY.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/EnumTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_EnumTypeAdapter_FACTORY_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_goog : Func :=
  { name := "com.google.gson.internal.bind.EnumTypeAdapter.FACTORY.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.seq
            .skip
            (.seq
              (.assign "rawType" (.call "getRawType" []))
              (.seq
                (.ifte
                  (.binop
                    "||"
                    (.unop "!" (.mcall (.name "Enum") "class" [(.name "rawType")]))
                    (.binop "==" (.name "rawType") (.field (.name "Enum") "class")))
                  (.ret (.lit .unit))
                  .skip)
                (.seq
                  (.ifte
                    (.unop "!" (.call "isEnum" []))
                    (.assign "rawType" (.call "getSuperclass" []))
                    .skip)
                  (.seq .skip (.seq (.assign "adapter" (.hole "op:cast")) (.ret (.name "adapter")))))))) }

/-- `com.google.gson.internal.bind.EnumTypeAdapter.FACTORY.TypeAdapterFactory$0.<init>:void()`  (from `internal/bind/EnumTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_EnumTypeAdapter_FACTORY_TypeAdapterFactory_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.EnumTypeAdapter.FACTORY.TypeAdapterFactory$0.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.IgnoreJRERequirement.<init>:void()`  (from `internal/bind/IgnoreJRERequirement.java`) -/
def f_com_google_gson_internal_bind_IgnoreJRERequirement__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.IgnoreJRERequirement.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.get:com.google.gson.TypeAdapterFactory()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_get_com_google_gson_TypeAdapterFactory__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.get:com.google.gson.TypeAdapterFactory()"
  , params := ["this"]
  , body := (.ret
            (.field
              (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
              "JAVA_TIME_FACTORY")) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.localDateTime:com.google.gson.TypeAdapter(com.google.gson.Gson)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_localDateTime_com_google_gson_TypeAdapter_com_google_gson_Gson_ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.localDateTime:com.google.gson.TypeAdapter(com.google.gson.Gson)"
  , params := ["gson"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "localDateAdapter"
                (.call "getAdapter" [(.field (.name "LocalDate") "class")]))
              (.seq
                .skip
                (.seq
                  (.assign
                    "localTimeAdapter"
                    (.call "getAdapter" [(.field (.name "LocalTime") "class")]))
                  (.ret (.call "nullSafe" [])))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetDateTime:com.google.gson.TypeAdapter(com.google.gson.Gson)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetDateTime_com_google_gson_TypeAdapter_com_google_gson_Gson_ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetDateTime:com.google.gson.TypeAdapter(com.google.gson.Gson)"
  , params := ["gson"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "localDateTimeAdapter"
                (.call
                  "com.google.gson.internal.bind.JavaTimeTypeAdapters.localDateTime:com.google.gson.TypeAdapter(com.google.gson.Gson)"
                  [(.name "gson")]))
              (.seq
                .skip
                (.seq
                  (.assign
                    "zoneOffsetAdapter"
                    (.call "getAdapter" [(.field (.name "ZoneOffset") "class")]))
                  (.ret (.call "nullSafe" [])))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetTime:com.google.gson.TypeAdapter(com.google.gson.Gson)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetTime_com_google_gson_TypeAdapter_com_google_gson_Gson_ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetTime:com.google.gson.TypeAdapter(com.google.gson.Gson)"
  , params := ["gson"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "localTimeAdapter"
                (.call "getAdapter" [(.field (.name "LocalTime") "class")]))
              (.seq
                .skip
                (.seq
                  (.assign
                    "zoneOffsetAdapter"
                    (.call "getAdapter" [(.field (.name "ZoneOffset") "class")]))
                  (.ret (.call "nullSafe" [])))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.zonedDateTime:com.google.gson.TypeAdapter(com.google.gson.Gson)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_zonedDateTime_com_google_gson_TypeAdapter_com_google_gson_Gson_ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.zonedDateTime:com.google.gson.TypeAdapter(com.google.gson.Gson)"
  , params := ["gson"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "localDateTimeAdapter"
                (.call
                  "com.google.gson.internal.bind.JavaTimeTypeAdapters.localDateTime:com.google.gson.TypeAdapter(com.google.gson.Gson)"
                  [(.name "gson")]))
              (.seq
                .skip
                (.seq
                  (.assign
                    "zoneOffsetAdapter"
                    (.call "getAdapter" [(.field (.name "ZoneOffset") "class")]))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "zoneIdAdapter"
                        (.call "getAdapter" [(.field (.name "ZoneId") "class")]))
                      (.ret (.call "nullSafe" [])))))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.requireNonNullField:java.lang.Object(java.lang.Object,java.lang.String,com.google.gson.stream.JsonReader)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_requireNonNullField_java_lang_Object_java_lang_Object_java_lang_Str : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.requireNonNullField:java.lang.Object(java.lang.Object,java.lang.String,com.google.gson.stream.JsonReader)"
  , params := ["field", "fieldName", "reader"]
  , body := (.seq
            (.ifte (.binop "==" (.name "field") (.lit .unit)) (.hole "control:THROW") .skip)
            (.ret (.name "field"))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
              "DURATION"
              (.hole "op:alloc"))
            (.seq
              (.expr
                (.mcall
                  (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                  "DURATION"
                  [(.hole "op:arrayInitializer")]))
              (.seq
                (.setField
                  (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                  "INSTANT"
                  (.hole "op:alloc"))
                (.seq
                  (.expr
                    (.mcall
                      (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                      "INSTANT"
                      [(.hole "op:arrayInitializer")]))
                  (.seq
                    (.setField
                      (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                      "LOCAL_DATE"
                      (.hole "op:alloc"))
                    (.seq
                      (.expr
                        (.mcall
                          (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                          "LOCAL_DATE"
                          [(.hole "op:arrayInitializer")]))
                      (.seq
                        (.setField
                          (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                          "LOCAL_TIME"
                          (.hole "op:alloc"))
                        (.seq
                          (.expr
                            (.mcall
                              (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                              "LOCAL_TIME"
                              [(.hole "op:arrayInitializer")]))
                          (.seq
                            (.setField
                              (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                              "MONTH_DAY"
                              (.hole "op:alloc"))
                            (.seq
                              (.expr
                                (.mcall
                                  (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                                  "MONTH_DAY"
                                  [(.hole "op:arrayInitializer")]))
                              (.seq
                                (.setField
                                  (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                                  "PERIOD"
                                  (.hole "op:alloc"))
                                (.seq
                                  (.expr
                                    (.mcall
                                      (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                                      "PERIOD"
                                      [(.hole "op:arrayInitializer")]))
                                  (.seq
                                    (.setField
                                      (.fnref "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                                      "YEAR"
                                      (.hole "op:alloc"))
                                    (.seq
                                      (.expr
                                        (.mcall
                                        (.fnref
                                        "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                                        "YEAR"
                                        [(.hole "op:arrayInitializer")]))
                                      (.seq
                                        (.setField
                                        (.fnref
                                        "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                                        "YEAR_MONTH"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref
                                        "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                                        "YEAR_MONTH"
                                        [(.hole "op:arrayInitializer")]))
                                        (.seq
                                        (.setField
                                        (.fnref
                                        "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                                        "ZONE_ID"
                                        (.call "nullSafe" []))
                                        (.seq
                                        (.setField
                                        (.fnref
                                        "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                                        "JAVA_TIME_FACTORY"
                                        (.hole "op:alloc"))
                                        (.expr
                                        (.mcall
                                        (.fnref
                                        "com.google.gson.internal.bind.JavaTimeTypeAdapters")
                                        "JAVA_TIME_FACTORY"
                                        [])))))))))))))))))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.DURATION.IntegerFieldsTypeAdapter$0.create:java.time.Duration(long[])`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_DURATION_IntegerFieldsTypeAdapter_0_create_java_time_Duration_long_ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.DURATION.IntegerFieldsTypeAdapter$0.create:java.time.Duration(long[])"
  , params := ["this", "values"]
  , body := (.ret
            (.call
              "ofSeconds"
              [(.index (.name "values") (.lit (.int 0))), (.index (.name "values") (.lit (.int 1)))])) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.DURATION.IntegerFieldsTypeAdapter$0.integerValues:long[](java.time.Duration)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_DURATION_IntegerFieldsTypeAdapter_0_integerValues_long___java_time_ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.DURATION.IntegerFieldsTypeAdapter$0.integerValues:long[](java.time.Duration)"
  , params := ["this", "duration"]
  , body := (.ret (.hole "op:arrayInitializer")) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.DURATION.IntegerFieldsTypeAdapter$0.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_DURATION_IntegerFieldsTypeAdapter_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.DURATION.IntegerFieldsTypeAdapter$0.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.INSTANT.IntegerFieldsTypeAdapter$1.create:java.time.Instant(long[])`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_INSTANT_IntegerFieldsTypeAdapter_1_create_java_time_Instant_long___ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.INSTANT.IntegerFieldsTypeAdapter$1.create:java.time.Instant(long[])"
  , params := ["this", "values"]
  , body := (.ret
            (.call
              "ofEpochSecond"
              [(.index (.name "values") (.lit (.int 0))), (.index (.name "values") (.lit (.int 1)))])) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.INSTANT.IntegerFieldsTypeAdapter$1.integerValues:long[](java.time.Instant)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_INSTANT_IntegerFieldsTypeAdapter_1_integerValues_long___java_time_I : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.INSTANT.IntegerFieldsTypeAdapter$1.integerValues:long[](java.time.Instant)"
  , params := ["this", "instant"]
  , body := (.ret (.hole "op:arrayInitializer")) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.INSTANT.IntegerFieldsTypeAdapter$1.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_INSTANT_IntegerFieldsTypeAdapter_1__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.INSTANT.IntegerFieldsTypeAdapter$1.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.LOCAL_DATE.IntegerFieldsTypeAdapter$2.create:java.time.LocalDate(long[])`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_LOCAL_DATE_IntegerFieldsTypeAdapter_2_create_java_time_LocalDate_lo : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.LOCAL_DATE.IntegerFieldsTypeAdapter$2.create:java.time.LocalDate(long[])"
  , params := ["this", "values"]
  , body := (.ret
            (.call
              "of"
              [ (.call "toIntExact" [(.index (.name "values") (.lit (.int 0)))])
              , (.call "toIntExact" [(.index (.name "values") (.lit (.int 1)))])
              , (.call "toIntExact" [(.index (.name "values") (.lit (.int 2)))]) ])) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.LOCAL_DATE.IntegerFieldsTypeAdapter$2.integerValues:long[](java.time.LocalDate)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_LOCAL_DATE_IntegerFieldsTypeAdapter_2_integerValues_long___java_tim : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.LOCAL_DATE.IntegerFieldsTypeAdapter$2.integerValues:long[](java.time.LocalDate)"
  , params := ["this", "localDate"]
  , body := (.ret (.hole "op:arrayInitializer")) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.LOCAL_DATE.IntegerFieldsTypeAdapter$2.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_LOCAL_DATE_IntegerFieldsTypeAdapter_2__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.LOCAL_DATE.IntegerFieldsTypeAdapter$2.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.LOCAL_TIME.IntegerFieldsTypeAdapter$3.create:java.time.LocalTime(long[])`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_LOCAL_TIME_IntegerFieldsTypeAdapter_3_create_java_time_LocalTime_lo : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.LOCAL_TIME.IntegerFieldsTypeAdapter$3.create:java.time.LocalTime(long[])"
  , params := ["this", "values"]
  , body := (.ret
            (.call
              "of"
              [ (.call "toIntExact" [(.index (.name "values") (.lit (.int 0)))])
              , (.call "toIntExact" [(.index (.name "values") (.lit (.int 1)))])
              , (.call "toIntExact" [(.index (.name "values") (.lit (.int 2)))])
              , (.call "toIntExact" [(.index (.name "values") (.lit (.int 3)))]) ])) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.LOCAL_TIME.IntegerFieldsTypeAdapter$3.integerValues:long[](java.time.LocalTime)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_LOCAL_TIME_IntegerFieldsTypeAdapter_3_integerValues_long___java_tim : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.LOCAL_TIME.IntegerFieldsTypeAdapter$3.integerValues:long[](java.time.LocalTime)"
  , params := ["this", "localTime"]
  , body := (.ret (.hole "op:arrayInitializer")) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.LOCAL_TIME.IntegerFieldsTypeAdapter$3.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_LOCAL_TIME_IntegerFieldsTypeAdapter_3__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.LOCAL_TIME.IntegerFieldsTypeAdapter$3.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.MONTH_DAY.IntegerFieldsTypeAdapter$4.create:java.time.MonthDay(long[])`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_MONTH_DAY_IntegerFieldsTypeAdapter_4_create_java_time_MonthDay_long : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.MONTH_DAY.IntegerFieldsTypeAdapter$4.create:java.time.MonthDay(long[])"
  , params := ["this", "values"]
  , body := (.ret
            (.call
              "of"
              [ (.call "toIntExact" [(.index (.name "values") (.lit (.int 0)))])
              , (.call "toIntExact" [(.index (.name "values") (.lit (.int 1)))]) ])) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.MONTH_DAY.IntegerFieldsTypeAdapter$4.integerValues:long[](java.time.MonthDay)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_MONTH_DAY_IntegerFieldsTypeAdapter_4_integerValues_long___java_time : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.MONTH_DAY.IntegerFieldsTypeAdapter$4.integerValues:long[](java.time.MonthDay)"
  , params := ["this", "monthDay"]
  , body := (.ret (.hole "op:arrayInitializer")) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.MONTH_DAY.IntegerFieldsTypeAdapter$4.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_MONTH_DAY_IntegerFieldsTypeAdapter_4__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.MONTH_DAY.IntegerFieldsTypeAdapter$4.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.PERIOD.IntegerFieldsTypeAdapter$5.create:java.time.Period(long[])`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_PERIOD_IntegerFieldsTypeAdapter_5_create_java_time_Period_long___ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.PERIOD.IntegerFieldsTypeAdapter$5.create:java.time.Period(long[])"
  , params := ["this", "values"]
  , body := (.ret
            (.call
              "of"
              [ (.call "toIntExact" [(.index (.name "values") (.lit (.int 0)))])
              , (.call "toIntExact" [(.index (.name "values") (.lit (.int 1)))])
              , (.call "toIntExact" [(.index (.name "values") (.lit (.int 2)))]) ])) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.PERIOD.IntegerFieldsTypeAdapter$5.integerValues:long[](java.time.Period)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_PERIOD_IntegerFieldsTypeAdapter_5_integerValues_long___java_time_Pe : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.PERIOD.IntegerFieldsTypeAdapter$5.integerValues:long[](java.time.Period)"
  , params := ["this", "period"]
  , body := (.ret (.hole "op:arrayInitializer")) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.PERIOD.IntegerFieldsTypeAdapter$5.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_PERIOD_IntegerFieldsTypeAdapter_5__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.PERIOD.IntegerFieldsTypeAdapter$5.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.YEAR.IntegerFieldsTypeAdapter$6.create:java.time.Year(long[])`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_YEAR_IntegerFieldsTypeAdapter_6_create_java_time_Year_long___ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.YEAR.IntegerFieldsTypeAdapter$6.create:java.time.Year(long[])"
  , params := ["this", "values"]
  , body := (.ret (.call "of" [(.call "toIntExact" [(.index (.name "values") (.lit (.int 0)))])])) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.YEAR.IntegerFieldsTypeAdapter$6.integerValues:long[](java.time.Year)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_YEAR_IntegerFieldsTypeAdapter_6_integerValues_long___java_time_Year : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.YEAR.IntegerFieldsTypeAdapter$6.integerValues:long[](java.time.Year)"
  , params := ["this", "year"]
  , body := (.ret (.hole "op:arrayInitializer")) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.YEAR.IntegerFieldsTypeAdapter$6.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_YEAR_IntegerFieldsTypeAdapter_6__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.YEAR.IntegerFieldsTypeAdapter$6.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.YEAR_MONTH.IntegerFieldsTypeAdapter$7.create:java.time.YearMonth(long[])`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_YEAR_MONTH_IntegerFieldsTypeAdapter_7_create_java_time_YearMonth_lo : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.YEAR_MONTH.IntegerFieldsTypeAdapter$7.create:java.time.YearMonth(long[])"
  , params := ["this", "values"]
  , body := (.ret
            (.call
              "of"
              [ (.call "toIntExact" [(.index (.name "values") (.lit (.int 0)))])
              , (.call "toIntExact" [(.index (.name "values") (.lit (.int 1)))]) ])) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.YEAR_MONTH.IntegerFieldsTypeAdapter$7.integerValues:long[](java.time.YearMonth)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_YEAR_MONTH_IntegerFieldsTypeAdapter_7_integerValues_long___java_tim : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.YEAR_MONTH.IntegerFieldsTypeAdapter$7.integerValues:long[](java.time.YearMonth)"
  , params := ["this", "yearMonth"]
  , body := (.ret (.hole "op:arrayInitializer")) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.YEAR_MONTH.IntegerFieldsTypeAdapter$7.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_YEAR_MONTH_IntegerFieldsTypeAdapter_7__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.YEAR_MONTH.IntegerFieldsTypeAdapter$7.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.ZONE_ID.TypeAdapter$8.read:java.time.ZoneId(com.google.gson.stream.JsonReader)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_ZONE_ID_TypeAdapter_8_read_java_time_ZoneId_com_google_gson_stream_ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.ZONE_ID.TypeAdapter$8.read:java.time.ZoneId(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.expr (.call "beginObject" []))
            (.seq
              .skip
              (.seq
                (.assign "id" (.lit .unit))
                (.seq
                  .skip
                  (.seq
                    (.assign "totalSeconds" (.lit .unit))
                    (.seq
                      (.loop
                        (.binop "!=" (.call "peek" []) (.field (.name "JsonToken") "END_OBJECT"))
                        (.seq
                          .skip
                          (.seq (.assign "name" (.call "nextName" [])) (.hole "control:SWITCH"))))
                      (.seq
                        (.expr (.call "endObject" []))
                        (.ifte
                          (.binop "!=" (.name "id") (.lit .unit))
                          (.ret (.call "of" [(.name "id")]))
                          (.ifte
                            (.binop "!=" (.name "totalSeconds") (.lit .unit))
                            (.ret (.call "ofTotalSeconds" [(.name "totalSeconds")]))
                            (.hole "control:THROW")))))))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.ZONE_ID.TypeAdapter$8.write:void(com.google.gson.stream.JsonWriter,java.time.ZoneId)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_ZONE_ID_TypeAdapter_8_write_void_com_google_gson_stream_JsonWriter_ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.ZONE_ID.TypeAdapter$8.write:void(com.google.gson.stream.JsonWriter,java.time.ZoneId)"
  , params := ["this", "out", "value"]
  , body := (.ifte
            (.hole "op:instanceOf")
            (.seq
              (.expr (.call "beginObject" []))
              (.seq
                (.expr (.call "name" [(.lit (.str "totalSeconds"))]))
                (.seq
                  (.expr (.call "value" [(.call "getTotalSeconds" [])]))
                  (.expr (.call "endObject" [])))))
            (.seq
              (.expr (.call "beginObject" []))
              (.seq
                (.expr (.call "name" [(.lit (.str "id"))]))
                (.seq (.expr (.call "value" [(.call "getId" [])])) (.expr (.call "endObject" [])))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.ZONE_ID.TypeAdapter$8.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_ZONE_ID_TypeAdapter_8__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.ZONE_ID.TypeAdapter$8.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.JAVA_TIME_FACTORY.TypeAdapterFactory$9.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_JAVA_TIME_FACTORY_TypeAdapterFactory_9_create_com_google_gson_TypeA : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.JAVA_TIME_FACTORY.TypeAdapterFactory$9.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.seq
            .skip
            (.seq
              (.assign "rawType" (.call "getRawType" []))
              (.seq
                (.ifte
                  (.unop "!" (.call "startsWith" [(.lit (.str "java.time."))]))
                  (.ret (.lit .unit))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "adapter" (.lit .unit))
                    (.seq
                      (.ifte
                        (.binop "==" (.name "rawType") (.field (.name "Duration") "class"))
                        (.assign "adapter" (.name "DURATION"))
                        (.ifte
                          (.binop "==" (.name "rawType") (.field (.name "Instant") "class"))
                          (.assign "adapter" (.name "INSTANT"))
                          (.ifte
                            (.binop "==" (.name "rawType") (.field (.name "LocalDate") "class"))
                            (.assign "adapter" (.name "LOCAL_DATE"))
                            (.ifte
                              (.binop "==" (.name "rawType") (.field (.name "LocalTime") "class"))
                              (.assign "adapter" (.name "LOCAL_TIME"))
                              (.ifte
                                (.binop
                                  "=="
                                  (.name "rawType")
                                  (.field (.name "LocalDateTime") "class"))
                                (.assign
                                  "adapter"
                                  (.mcall (.name "this") "outerClass" [(.name "gson")]))
                                (.ifte
                                  (.binop
                                    "=="
                                    (.name "rawType")
                                    (.field (.name "MonthDay") "class"))
                                  (.assign "adapter" (.name "MONTH_DAY"))
                                  (.ifte
                                    (.binop
                                      "=="
                                      (.name "rawType")
                                      (.field (.name "OffsetDateTime") "class"))
                                    (.assign
                                      "adapter"
                                      (.mcall (.name "this") "outerClass" [(.name "gson")]))
                                    (.ifte
                                      (.binop
                                        "=="
                                        (.name "rawType")
                                        (.field (.name "OffsetTime") "class"))
                                      (.assign
                                        "adapter"
                                        (.mcall (.name "this") "outerClass" [(.name "gson")]))
                                      (.ifte
                                        (.binop
                                        "=="
                                        (.name "rawType")
                                        (.field (.name "Period") "class"))
                                        (.assign "adapter" (.name "PERIOD"))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.name "rawType")
                                        (.field (.name "Year") "class"))
                                        (.assign "adapter" (.name "YEAR"))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.name "rawType")
                                        (.field (.name "YearMonth") "class"))
                                        (.assign "adapter" (.name "YEAR_MONTH"))
                                        (.ifte
                                        (.binop
                                        "||"
                                        (.binop
                                        "=="
                                        (.name "rawType")
                                        (.field (.name "ZoneId") "class"))
                                        (.binop
                                        "=="
                                        (.name "rawType")
                                        (.field (.name "ZoneOffset") "class")))
                                        (.assign "adapter" (.name "ZONE_ID"))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.name "rawType")
                                        (.field (.name "ZonedDateTime") "class"))
                                        (.assign
                                        "adapter"
                                        (.mcall (.name "this") "outerClass" [(.name "gson")]))
                                        .skip)))))))))))))
                      (.seq
                        .skip
                        (.seq (.assign "result" (.hole "op:cast")) (.ret (.name "result")))))))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.JAVA_TIME_FACTORY.TypeAdapterFactory$9.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_JAVA_TIME_FACTORY_TypeAdapterFactory_9__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.JAVA_TIME_FACTORY.TypeAdapterFactory$9.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.localDateTime.TypeAdapter$0.read:java.time.LocalDateTime(com.google.gson.stream.JsonReader)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_localDateTime_TypeAdapter_0_read_java_time_LocalDateTime_com_google : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.localDateTime.TypeAdapter$0.read:java.time.LocalDateTime(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              (.assign "localDate" (.lit .unit))
              (.seq
                .skip
                (.seq
                  (.assign "localTime" (.lit .unit))
                  (.seq
                    (.expr (.call "beginObject" []))
                    (.seq
                      (.loop
                        (.binop "!=" (.call "peek" []) (.field (.name "JsonToken") "END_OBJECT"))
                        (.seq
                          .skip
                          (.seq (.assign "name" (.call "nextName" [])) (.hole "control:SWITCH"))))
                      (.seq
                        (.expr (.call "endObject" []))
                        (.ret
                          (.call
                            "of"
                            [ (.mcall
                                (.name "this")
                                "outerClass"
                                [(.name "localDate"), (.lit (.str "date")), (.name "in")])
                            , (.mcall
                                (.name "this")
                                "outerClass"
                                [(.name "localTime"), (.lit (.str "time")), (.name "in")]) ]))))))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.localDateTime.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.time.LocalDateTime)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_localDateTime_TypeAdapter_0_write_void_com_google_gson_stream_JsonW : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.localDateTime.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.time.LocalDateTime)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.expr (.call "beginObject" []))
            (.seq
              (.expr (.call "name" [(.lit (.str "date"))]))
              (.seq
                (.expr
                  (.mcall
                    (.name "this")
                    "localDateAdapter"
                    [(.name "out"), (.call "toLocalDate" [])]))
                (.seq
                  (.expr (.call "name" [(.lit (.str "time"))]))
                  (.seq
                    (.expr
                      (.mcall
                        (.name "this")
                        "localTimeAdapter"
                        [(.name "out"), (.call "toLocalTime" [])]))
                    (.expr (.call "endObject" []))))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.localDateTime.TypeAdapter$0.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_localDateTime_TypeAdapter_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.localDateTime.TypeAdapter$0.<init>:void()"
  , params := ["this", "localDateAdapter", "localTimeAdapter"]
  , body := (.seq
            (.setField (.name "this") "localDateAdapter" (.name "localDateAdapter"))
            (.setField (.name "this") "localTimeAdapter" (.name "localTimeAdapter"))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetDateTime.TypeAdapter$0.read:java.time.OffsetDateTime(com.google.gson.stream.JsonReader)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetDateTime_TypeAdapter_0_read_java_time_OffsetDateTime_com_goog : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetDateTime.TypeAdapter$0.read:java.time.OffsetDateTime(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.expr (.call "beginObject" []))
            (.seq
              .skip
              (.seq
                (.assign "localDateTime" (.lit .unit))
                (.seq
                  .skip
                  (.seq
                    (.assign "zoneOffset" (.lit .unit))
                    (.seq
                      (.loop
                        (.binop "!=" (.call "peek" []) (.field (.name "JsonToken") "END_OBJECT"))
                        (.seq
                          .skip
                          (.seq (.assign "name" (.call "nextName" [])) (.hole "control:SWITCH"))))
                      (.seq
                        (.expr (.call "endObject" []))
                        (.ret
                          (.call
                            "of"
                            [ (.mcall
                                (.name "this")
                                "outerClass"
                                [(.name "localDateTime"), (.lit (.str "dateTime")), (.name "in")])
                            , (.mcall
                                (.name "this")
                                "outerClass"
                                [(.name "zoneOffset"), (.lit (.str "offset")), (.name "in")]) ]))))))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetDateTime.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.time.OffsetDateTime)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetDateTime_TypeAdapter_0_write_void_com_google_gson_stream_Json : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetDateTime.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.time.OffsetDateTime)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.expr (.call "beginObject" []))
            (.seq
              (.expr (.call "name" [(.lit (.str "dateTime"))]))
              (.seq
                (.expr
                  (.mcall
                    (.name "this")
                    "localDateTimeAdapter"
                    [(.name "out"), (.call "toLocalDateTime" [])]))
                (.seq
                  (.expr (.call "name" [(.lit (.str "offset"))]))
                  (.seq
                    (.expr
                      (.mcall
                        (.name "this")
                        "zoneOffsetAdapter"
                        [(.name "out"), (.call "getOffset" [])]))
                    (.expr (.call "endObject" []))))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetDateTime.TypeAdapter$0.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetDateTime_TypeAdapter_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetDateTime.TypeAdapter$0.<init>:void()"
  , params := ["this", "localDateTimeAdapter", "zoneOffsetAdapter"]
  , body := (.seq
            (.setField (.name "this") "localDateTimeAdapter" (.name "localDateTimeAdapter"))
            (.setField (.name "this") "zoneOffsetAdapter" (.name "zoneOffsetAdapter"))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetTime.TypeAdapter$0.read:java.time.OffsetTime(com.google.gson.stream.JsonReader)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetTime_TypeAdapter_0_read_java_time_OffsetTime_com_google_gson_ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetTime.TypeAdapter$0.read:java.time.OffsetTime(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.expr (.call "beginObject" []))
            (.seq
              .skip
              (.seq
                (.assign "localTime" (.lit .unit))
                (.seq
                  .skip
                  (.seq
                    (.assign "zoneOffset" (.lit .unit))
                    (.seq
                      (.loop
                        (.binop "!=" (.call "peek" []) (.field (.name "JsonToken") "END_OBJECT"))
                        (.seq
                          .skip
                          (.seq (.assign "name" (.call "nextName" [])) (.hole "control:SWITCH"))))
                      (.seq
                        (.expr (.call "endObject" []))
                        (.ret
                          (.call
                            "of"
                            [ (.mcall
                                (.name "this")
                                "outerClass"
                                [(.name "localTime"), (.lit (.str "time")), (.name "in")])
                            , (.mcall
                                (.name "this")
                                "outerClass"
                                [(.name "zoneOffset"), (.lit (.str "offset")), (.name "in")]) ]))))))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetTime.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.time.OffsetTime)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetTime_TypeAdapter_0_write_void_com_google_gson_stream_JsonWrit : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetTime.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.time.OffsetTime)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.expr (.call "beginObject" []))
            (.seq
              (.expr (.call "name" [(.lit (.str "time"))]))
              (.seq
                (.expr
                  (.mcall
                    (.name "this")
                    "localTimeAdapter"
                    [(.name "out"), (.call "toLocalTime" [])]))
                (.seq
                  (.expr (.call "name" [(.lit (.str "offset"))]))
                  (.seq
                    (.expr
                      (.mcall
                        (.name "this")
                        "zoneOffsetAdapter"
                        [(.name "out"), (.call "getOffset" [])]))
                    (.expr (.call "endObject" []))))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetTime.TypeAdapter$0.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetTime_TypeAdapter_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.offsetTime.TypeAdapter$0.<init>:void()"
  , params := ["this", "localTimeAdapter", "zoneOffsetAdapter"]
  , body := (.seq
            (.setField (.name "this") "localTimeAdapter" (.name "localTimeAdapter"))
            (.setField (.name "this") "zoneOffsetAdapter" (.name "zoneOffsetAdapter"))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.zonedDateTime.TypeAdapter$0.read:java.time.ZonedDateTime(com.google.gson.stream.JsonReader)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_zonedDateTime_TypeAdapter_0_read_java_time_ZonedDateTime_com_google : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.zonedDateTime.TypeAdapter$0.read:java.time.ZonedDateTime(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.expr (.call "beginObject" []))
            (.seq
              .skip
              (.seq
                (.assign "localDateTime" (.lit .unit))
                (.seq
                  .skip
                  (.seq
                    (.assign "zoneOffset" (.lit .unit))
                    (.seq
                      .skip
                      (.seq
                        (.assign "zoneId" (.lit .unit))
                        (.seq
                          (.loop
                            (.binop
                              "!="
                              (.call "peek" [])
                              (.field (.name "JsonToken") "END_OBJECT"))
                            (.seq
                              .skip
                              (.seq (.assign "name" (.call "nextName" [])) (.hole "control:SWITCH"))))
                          (.seq
                            (.expr (.call "endObject" []))
                            (.ret
                              (.call
                                "ofInstant"
                                [ (.mcall
                                    (.name "this")
                                    "outerClass"
                                    [ (.name "localDateTime")
                                    , (.lit (.str "dateTime"))
                                    , (.name "in") ])
                                , (.mcall
                                    (.name "this")
                                    "outerClass"
                                    [(.name "zoneOffset"), (.lit (.str "offset")), (.name "in")])
                                , (.mcall
                                    (.name "this")
                                    "outerClass"
                                    [(.name "zoneId"), (.lit (.str "zone")), (.name "in")]) ]))))))))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.zonedDateTime.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.time.ZonedDateTime)`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_zonedDateTime_TypeAdapter_0_write_void_com_google_gson_stream_JsonW : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.zonedDateTime.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.time.ZonedDateTime)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "value") (.lit .unit))
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              (.expr (.call "beginObject" []))
              (.seq
                (.expr (.call "name" [(.lit (.str "dateTime"))]))
                (.seq
                  (.expr
                    (.mcall
                      (.name "this")
                      "localDateTimeAdapter"
                      [(.name "out"), (.call "toLocalDateTime" [])]))
                  (.seq
                    (.expr (.call "name" [(.lit (.str "offset"))]))
                    (.seq
                      (.expr
                        (.mcall
                          (.name "this")
                          "zoneOffsetAdapter"
                          [(.name "out"), (.call "getOffset" [])]))
                      (.seq
                        (.expr (.call "name" [(.lit (.str "zone"))]))
                        (.seq
                          (.expr
                            (.mcall
                              (.name "this")
                              "zoneIdAdapter"
                              [(.name "out"), (.call "getZone" [])]))
                          (.expr (.call "endObject" [])))))))))) }

/-- `com.google.gson.internal.bind.JavaTimeTypeAdapters.zonedDateTime.TypeAdapter$0.<init>:void()`  (from `internal/bind/JavaTimeTypeAdapters.java`) -/
def f_com_google_gson_internal_bind_JavaTimeTypeAdapters_zonedDateTime_TypeAdapter_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JavaTimeTypeAdapters.zonedDateTime.TypeAdapter$0.<init>:void()"
  , params := ["this", "localDateTimeAdapter", "zoneIdAdapter", "zoneOffsetAdapter"]
  , body := (.seq
            (.setField (.name "this") "localDateTimeAdapter" (.name "localDateTimeAdapter"))
            (.seq
              (.setField (.name "this") "zoneIdAdapter" (.name "zoneIdAdapter"))
              (.setField (.name "this") "zoneOffsetAdapter" (.name "zoneOffsetAdapter")))) }

/-- `com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory$DummyTypeAdapterFactory.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/JsonAdapterAnnotationTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_DummyTypeAdapterFactory_create_com_google_gson_T : Func :=
  { name := "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory$DummyTypeAdapterFactory.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "type"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory$DummyTypeAdapterFactory.<init>:void()`  (from `internal/bind/JsonAdapterAnnotationTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_DummyTypeAdapterFactory__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory$DummyTypeAdapterFactory.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.<init>:void(com.google.gson.internal.ConstructorConstructor)`  (from `internal/bind/JsonAdapterAnnotationTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory__init__void_com_google_gson_internal_Constructor : Func :=
  { name := "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.<init>:void(com.google.gson.internal.ConstructorConstructor)"
  , params := ["this", "constructorConstructor"]
  , body := (.seq
            (.setField (.name "this") "constructorConstructor" (.name "constructorConstructor"))
            (.seq
              (.setField (.name "this") "adapterFactoryMap" (.hole "op:alloc"))
              (.expr (.mcall (.name "this") "adapterFactoryMap" [])))) }

/-- `com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.getAnnotation:com.google.gson.annotations.JsonAdapter(java.lang.Class)`  (from `internal/bind/JsonAdapterAnnotationTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_getAnnotation_com_google_gson_annotations_JsonAd : Func :=
  { name := "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.getAnnotation:com.google.gson.annotations.JsonAdapter(java.lang.Class)"
  , params := ["rawType"]
  , body := (.ret (.call "getAnnotation" [(.field (.name "JsonAdapter") "class")])) }

/-- `com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/JsonAdapterAnnotationTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_create_com_google_gson_TypeAdapter_com_google_gs : Func :=
  { name := "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "targetType"]
  , body := (.seq
            .skip
            (.seq
              (.assign "rawType" (.call "getRawType" []))
              (.seq
                .skip
                (.seq
                  (.assign
                    "annotation"
                    (.call
                      "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.getAnnotation:com.google.gson.annotations.JsonAdapter(java.lang.Class)"
                      [(.name "rawType")]))
                  (.seq
                    (.ifte
                      (.binop "==" (.name "annotation") (.lit .unit))
                      (.ret (.lit .unit))
                      .skip)
                    (.ret (.hole "op:cast"))))))) }

/-- `com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.createAdapter:java.lang.Object(com.google.gson.internal.ConstructorConstructor,java.lang.Class)`  (from `internal/bind/JsonAdapterAnnotationTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_createAdapter_java_lang_Object_com_google_gson_i : Func :=
  { name := "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.createAdapter:java.lang.Object(com.google.gson.internal.ConstructorConstructor,java.lang.Class)"
  , params := ["constructorConstructor", "adapterClass"]
  , body := (.seq
            .skip
            (.seq (.assign "allowUnsafe" (.lit (.bool true))) (.ret (.call "construct" [])))) }

/-- `com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.putFactoryAndGetCurrent:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapterFactory)`  (from `internal/bind/JsonAdapterAnnotationTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_putFactoryAndGetCurrent_com_google_gson_TypeAdap : Func :=
  { name := "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.putFactoryAndGetCurrent:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapterFactory)"
  , params := ["this", "rawType", "factory"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "existingFactory"
                (.mcall (.name "this") "adapterFactoryMap" [(.name "rawType"), (.name "factory")]))
              (.ret
                (.cond
                  (.binop "!=" (.name "existingFactory") (.lit .unit))
                  (.name "existingFactory")
                  (.name "factory"))))) }

/-- `com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.getTypeAdapter:com.google.gson.TypeAdapter(com.google.gson.internal.ConstructorConstructor,com.google.gson.Gson,com.google.gson.reflect.TypeToken,com.google.gson.annotations.JsonAdapter,boolean)`  (from `internal/bind/JsonAdapterAnnotationTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_getTypeAdapter_com_google_gson_TypeAdapter_com_g : Func :=
  { name := "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.getTypeAdapter:com.google.gson.TypeAdapter(com.google.gson.internal.ConstructorConstructor,com.google.gson.Gson,com.google.gson.reflect.TypeToken,com.google.gson.annotations.JsonAdapter,boolean)"
  , params := ["this", "constructorConstructor", "gson", "type", "annotation", "isClassAnnotation"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "instance"
                (.call
                  "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.createAdapter:java.lang.Object(com.google.gson.internal.ConstructorConstructor,java.lang.Class)"
                  [(.name "constructorConstructor"), (.call "value" [])]))
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    (.assign "nullSafe" (.call "nullSafe" []))
                    (.seq
                      (.ifte
                        (.hole "op:instanceOf")
                        (.assign "typeAdapter" (.hole "op:cast"))
                        (.ifte
                          (.hole "op:instanceOf")
                          (.seq
                            .skip
                            (.seq
                              (.assign "factory" (.hole "op:cast"))
                              (.seq
                                (.ifte
                                  (.name "isClassAnnotation")
                                  (.assign
                                    "factory"
                                    (.call
                                      "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.putFactoryAndGetCurrent:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapterFactory)"
                                      [(.call "getRawType" []), (.name "factory")]))
                                  .skip)
                                (.assign
                                  "typeAdapter"
                                  (.call "create" [(.name "gson"), (.name "type")])))))
                          (.ifte
                            (.binop "||" (.hole "op:instanceOf") (.hole "op:instanceOf"))
                            (.seq
                              .skip
                              (.seq
                                (.assign
                                  "serializer"
                                  (.cond (.hole "op:instanceOf") (.hole "op:cast") (.lit .unit)))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign
                                      "deserializer"
                                      (.cond (.hole "op:instanceOf") (.hole "op:cast") (.lit .unit)))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.ifte
                                        (.name "isClassAnnotation")
                                        (.assign
                                        "skipPast"
                                        (.field
                                        (.fnref
                                        "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory")
                                        "TREE_TYPE_CLASS_DUMMY_FACTORY"))
                                        (.assign
                                        "skipPast"
                                        (.field
                                        (.fnref
                                        "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory")
                                        "TREE_TYPE_FIELD_DUMMY_FACTORY")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "tempAdapter" (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "<init>"
                                        [ (.name "serializer")
                                        , (.name "deserializer")
                                        , (.name "gson")
                                        , (.name "type")
                                        , (.name "skipPast")
                                        , (.name "nullSafe") ]))
                                        (.seq
                                        (.assign "typeAdapter" (.name "tempAdapter"))
                                        (.assign "nullSafe" (.lit (.bool false)))))))))))))
                            (.hole "control:THROW"))))
                      (.seq
                        (.ifte
                          (.binop
                            "&&"
                            (.binop "!=" (.name "typeAdapter") (.lit .unit))
                            (.name "nullSafe"))
                          (.assign "typeAdapter" (.call "nullSafe" []))
                          .skip)
                        (.ret (.name "typeAdapter"))))))))) }

/-- `com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.areSameFactories:boolean(com.google.gson.TypeAdapterFactory,com.google.gson.TypeAdapterFactory)`  (from `internal/bind/JsonAdapterAnnotationTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_areSameFactories_boolean_com_google_gson_TypeAda : Func :=
  { name := "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.areSameFactories:boolean(com.google.gson.TypeAdapterFactory,com.google.gson.TypeAdapterFactory)"
  , params := ["a", "b"]
  , body := (.ret (.binop "==" (.name "a") (.name "b"))) }

/-- `com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.isClassJsonAdapterFactory:boolean(com.google.gson.reflect.TypeToken,com.google.gson.TypeAdapterFactory)`  (from `internal/bind/JsonAdapterAnnotationTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_isClassJsonAdapterFactory_boolean_com_google_gso : Func :=
  { name := "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.isClassJsonAdapterFactory:boolean(com.google.gson.reflect.TypeToken,com.google.gson.TypeAdapterFactory)"
  , params := ["this", "type", "factory"]
  , body := (.seq
            (.expr (.call "requireNonNull" [(.name "type")]))
            (.seq
              (.expr (.call "requireNonNull" [(.name "factory")]))
              (.seq
                (.ifte
                  (.binop
                    "=="
                    (.name "factory")
                    (.field
                      (.fnref
                        "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory")
                      "TREE_TYPE_CLASS_DUMMY_FACTORY"))
                  (.ret (.lit (.bool true)))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "rawType" (.call "getRawType" []))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "existingFactory"
                          (.mcall (.name "this") "adapterFactoryMap" [(.name "rawType")]))
                        (.seq
                          (.ifte
                            (.binop "!=" (.name "existingFactory") (.lit .unit))
                            (.ret
                              (.call
                                "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.areSameFactories:boolean(com.google.gson.TypeAdapterFactory,com.google.gson.TypeAdapterFactory)"
                                [(.name "existingFactory"), (.name "factory")]))
                            .skip)
                          (.seq
                            .skip
                            (.seq
                              (.assign
                                "annotation"
                                (.call
                                  "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.getAnnotation:com.google.gson.annotations.JsonAdapter(java.lang.Class)"
                                  [(.name "rawType")]))
                              (.seq
                                (.ifte
                                  (.binop "==" (.name "annotation") (.lit .unit))
                                  (.ret (.lit (.bool false)))
                                  .skip)
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "adapterClass" (.call "value" []))
                                    (.seq
                                      (.ifte
                                        (.unop
                                        "!"
                                        (.mcall
                                        (.name "TypeAdapterFactory")
                                        "class"
                                        [(.name "adapterClass")]))
                                        (.ret (.lit (.bool false)))
                                        .skip)
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "adapter"
                                        (.mcall
                                        (.name "this")
                                        "constructorConstructor"
                                        [ (.field (.name "this") "constructorConstructor")
                                        , (.name "adapterClass") ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "newFactory" (.hole "op:cast"))
                                        (.seq
                                        (.assign
                                        "newFactory"
                                        (.call
                                        "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.putFactoryAndGetCurrent:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapterFactory)"
                                        [(.name "rawType"), (.name "newFactory")]))
                                        (.ret
                                        (.call
                                        "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.areSameFactories:boolean(com.google.gson.TypeAdapterFactory,com.google.gson.TypeAdapterFactory)"
                                        [(.name "newFactory"), (.name "factory")]))))))))))))))))))))) }

/-- `com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory")
              "TREE_TYPE_CLASS_DUMMY_FACTORY"
              (.hole "op:alloc"))
            (.seq
              (.expr
                (.mcall
                  (.fnref "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory")
                  "TREE_TYPE_CLASS_DUMMY_FACTORY"
                  []))
              (.seq
                (.setField
                  (.fnref "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory")
                  "TREE_TYPE_FIELD_DUMMY_FACTORY"
                  (.hole "op:alloc"))
                (.expr
                  (.mcall
                    (.fnref "com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory")
                    "TREE_TYPE_FIELD_DUMMY_FACTORY"
                    []))))) }

/-- `com.google.gson.internal.bind.JsonElementTypeAdapter.<init>:void()`  (from `internal/bind/JsonElementTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_JsonElementTypeAdapter__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonElementTypeAdapter.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JsonElementTypeAdapter.tryBeginNesting:com.google.gson.JsonElement(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)`  (from `internal/bind/JsonElementTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_JsonElementTypeAdapter_tryBeginNesting_com_google_gson_JsonElement_com_google_gson_strea : Func :=
  { name := "com.google.gson.internal.bind.JsonElementTypeAdapter.tryBeginNesting:com.google.gson.JsonElement(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)"
  , params := ["this", "in", "peeked"]
  , body := (.hole "control:SWITCH") }

/-- `com.google.gson.internal.bind.JsonElementTypeAdapter.readTerminal:com.google.gson.JsonElement(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)`  (from `internal/bind/JsonElementTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_JsonElementTypeAdapter_readTerminal_com_google_gson_JsonElement_com_google_gson_stream_J : Func :=
  { name := "com.google.gson.internal.bind.JsonElementTypeAdapter.readTerminal:com.google.gson.JsonElement(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)"
  , params := ["this", "in", "peeked"]
  , body := (.hole "control:SWITCH") }

/-- `com.google.gson.internal.bind.JsonElementTypeAdapter.read:com.google.gson.JsonElement(com.google.gson.stream.JsonReader)`  (from `internal/bind/JsonElementTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_JsonElementTypeAdapter_read_com_google_gson_JsonElement_com_google_gson_stream_JsonReade : Func :=
  { name := "com.google.gson.internal.bind.JsonElementTypeAdapter.read:com.google.gson.JsonElement(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.hole "op:instanceOf")
              (.ret
                (.call
                  "com.google.gson.internal.bind.JsonTreeReader.nextJsonElement:com.google.gson.JsonElement()"
                  []))
              .skip)
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign "peeked" (.call "peek" []))
                  (.seq
                    (.assign
                      "current"
                      (.call
                        "com.google.gson.internal.bind.JsonElementTypeAdapter.tryBeginNesting:com.google.gson.JsonElement(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)"
                        [(.name "in"), (.name "peeked")]))
                    (.seq
                      (.ifte
                        (.binop "==" (.name "current") (.lit .unit))
                        (.ret
                          (.call
                            "com.google.gson.internal.bind.JsonElementTypeAdapter.readTerminal:com.google.gson.JsonElement(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)"
                            [(.name "in"), (.name "peeked")]))
                        .skip)
                      (.seq
                        .skip
                        (.seq
                          (.assign "stack" (.hole "op:alloc"))
                          (.seq
                            (.expr (.call "<init>" []))
                            (.loop
                              (.lit (.bool true))
                              (.seq
                                (.loop
                                  (.call "hasNext" [])
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign "name" (.lit .unit))
                                      (.seq
                                        (.ifte
                                        (.hole "op:instanceOf")
                                        (.assign "name" (.call "nextName" []))
                                        .skip)
                                        (.seq
                                        (.assign "peeked" (.call "peek" []))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "value"
                                        (.call
                                        "com.google.gson.internal.bind.JsonElementTypeAdapter.tryBeginNesting:com.google.gson.JsonElement(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)"
                                        [(.name "in"), (.name "peeked")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "isNesting"
                                        (.binop "!=" (.name "value") (.lit .unit)))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "value") (.lit .unit))
                                        (.assign
                                        "value"
                                        (.call
                                        "com.google.gson.internal.bind.JsonElementTypeAdapter.readTerminal:com.google.gson.JsonElement(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)"
                                        [(.name "in"), (.name "peeked")]))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.hole "op:instanceOf")
                                        (.expr (.call "add" [(.name "value")]))
                                        (.expr (.call "add" [(.name "name"), (.name "value")])))
                                        (.ifte
                                        (.name "isNesting")
                                        (.seq
                                        (.expr (.call "addLast" [(.name "current")]))
                                        (.assign "current" (.name "value")))
                                        .skip))))))))))))
                                (.seq
                                  (.ifte
                                    (.hole "op:instanceOf")
                                    (.expr (.call "endArray" []))
                                    (.expr (.call "endObject" [])))
                                  (.ifte
                                    (.call "isEmpty" [])
                                    (.ret (.name "current"))
                                    (.assign "current" (.call "removeLast" []))))))))))))))) }

/-- `com.google.gson.internal.bind.JsonElementTypeAdapter.write:void(com.google.gson.stream.JsonWriter,com.google.gson.JsonElement)`  (from `internal/bind/JsonElementTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_JsonElementTypeAdapter_write_void_com_google_gson_stream_JsonWriter_com_google_gson_Json : Func :=
  { name := "com.google.gson.internal.bind.JsonElementTypeAdapter.write:void(com.google.gson.stream.JsonWriter,com.google.gson.JsonElement)"
  , params := ["this", "out", "value"]
  , body := (.ifte
            (.binop "||" (.binop "==" (.name "value") (.lit .unit)) (.call "isJsonNull" []))
            (.expr (.call "nullValue" []))
            (.ifte
              (.call "isJsonPrimitive" [])
              (.seq
                .skip
                (.seq
                  (.assign "primitive" (.call "getAsJsonPrimitive" []))
                  (.ifte
                    (.call "isNumber" [])
                    (.expr (.call "value" [(.call "getAsNumber" [])]))
                    (.ifte
                      (.call "isBoolean" [])
                      (.expr (.call "value" [(.call "getAsBoolean" [])]))
                      (.expr (.call "value" [(.call "getAsString" [])]))))))
              (.ifte
                (.call "isJsonArray" [])
                (.seq
                  (.expr (.call "beginArray" []))
                  (.seq
                    .skip
                    (.seq
                      (.assign "$iterLocal0" (.call "iterator" []))
                      (.seq
                        (.loop
                          (.call "hasNext" [])
                          (.seq
                            .skip
                            (.seq
                              (.assign "e" (.call "next" []))
                              (.expr
                                (.call
                                  "com.google.gson.internal.bind.JsonElementTypeAdapter.write:void(com.google.gson.stream.JsonWriter,com.google.gson.JsonElement)"
                                  [(.name "out"), (.name "e")])))))
                        (.expr (.call "endArray" []))))))
                (.ifte
                  (.call "isJsonObject" [])
                  (.seq
                    (.expr (.call "beginObject" []))
                    (.seq
                      .skip
                      (.seq
                        (.assign "$iterLocal1" (.call "iterator" []))
                        (.seq
                          (.loop
                            (.call "hasNext" [])
                            (.seq
                              .skip
                              (.seq
                                (.assign "e" (.call "next" []))
                                (.seq
                                  (.expr (.call "name" [(.call "getKey" [])]))
                                  (.expr
                                    (.call
                                      "com.google.gson.internal.bind.JsonElementTypeAdapter.write:void(com.google.gson.stream.JsonWriter,com.google.gson.JsonElement)"
                                      [(.name "out"), (.call "getValue" [])]))))))
                          (.expr (.call "endObject" []))))))
                  (.hole "control:THROW"))))) }

/-- `com.google.gson.internal.bind.JsonElementTypeAdapter.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_JsonElementTypeAdapter__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonElementTypeAdapter.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.bind.JsonElementTypeAdapter")
              "ADAPTER"
              (.hole "op:alloc"))
            (.expr
              (.mcall (.fnref "com.google.gson.internal.bind.JsonElementTypeAdapter") "ADAPTER" []))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.<init>:void(com.google.gson.JsonElement)`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader__init__void_com_google_gson_JsonElement_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.<init>:void(com.google.gson.JsonElement)"
  , params := ["this", "element"]
  , body := (.seq
            (.setField (.name "this") "stack" (.hole "op:alloc"))
            (.seq
              (.setField (.name "this") "stackSize" (.lit (.int 0)))
              (.seq
                (.setField (.name "this") "pathNames" (.hole "op:alloc"))
                (.seq
                  (.setField (.name "this") "pathIndices" (.hole "op:alloc"))
                  (.seq
                    (.expr
                      (.call
                        "<init>"
                        [ (.field
                            (.fnref "com.google.gson.internal.bind.JsonTreeReader")
                            "UNREADABLE_READER") ]))
                    (.expr (.call "push" [(.name "element")]))))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.beginArray:void()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_beginArray_void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.beginArray:void()"
  , params := ["this"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.bind.JsonTreeReader.expect:void(com.google.gson.stream.JsonToken)"
                [(.field (.name "JsonToken") "BEGIN_ARRAY")]))
            (.seq
              .skip
              (.seq
                (.assign "array" (.hole "op:cast"))
                (.seq
                  (.expr
                    (.call
                      "com.google.gson.internal.bind.JsonTreeReader.push:void(java.lang.Object)"
                      [(.call "iterator" [])]))
                  (.setIndex
                    (.field (.name "this") "pathIndices")
                    (.binop "-" (.field (.name "this") "stackSize") (.lit (.int 1)))
                    (.lit (.int 0))))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.endArray:void()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_endArray_void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.endArray:void()"
  , params := ["this"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.bind.JsonTreeReader.expect:void(com.google.gson.stream.JsonToken)"
                [(.field (.name "JsonToken") "END_ARRAY")]))
            (.seq
              (.expr
                (.call
                  "com.google.gson.internal.bind.JsonTreeReader.popStack:java.lang.Object()"
                  []))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.bind.JsonTreeReader.popStack:java.lang.Object()"
                    []))
                (.ifte
                  (.binop ">" (.field (.name "this") "stackSize") (.lit (.int 0)))
                  (.expr (.hole "op:postIncrement"))
                  .skip)))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.beginObject:void()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_beginObject_void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.beginObject:void()"
  , params := ["this"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.bind.JsonTreeReader.expect:void(com.google.gson.stream.JsonToken)"
                [(.field (.name "JsonToken") "BEGIN_OBJECT")]))
            (.seq
              .skip
              (.seq
                (.assign "object" (.hole "op:cast"))
                (.expr
                  (.call
                    "com.google.gson.internal.bind.JsonTreeReader.push:void(java.lang.Object)"
                    [(.call "iterator" [])]))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.endObject:void()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_endObject_void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.endObject:void()"
  , params := ["this"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.bind.JsonTreeReader.expect:void(com.google.gson.stream.JsonToken)"
                [(.field (.name "JsonToken") "END_OBJECT")]))
            (.seq
              (.setIndex
                (.field (.name "this") "pathNames")
                (.binop "-" (.field (.name "this") "stackSize") (.lit (.int 1)))
                (.lit .unit))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.bind.JsonTreeReader.popStack:java.lang.Object()"
                    []))
                (.seq
                  (.expr
                    (.call
                      "com.google.gson.internal.bind.JsonTreeReader.popStack:java.lang.Object()"
                      []))
                  (.ifte
                    (.binop ">" (.field (.name "this") "stackSize") (.lit (.int 0)))
                    (.expr (.hole "op:postIncrement"))
                    .skip))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.hasNext:boolean()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_hasNext_boolean__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.hasNext:boolean()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "token"
                (.call
                  "com.google.gson.internal.bind.JsonTreeReader.peek:com.google.gson.stream.JsonToken()"
                  []))
              (.ret
                (.binop
                  "&&"
                  (.binop
                    "&&"
                    (.binop "!=" (.name "token") (.field (.name "JsonToken") "END_OBJECT"))
                    (.binop "!=" (.name "token") (.field (.name "JsonToken") "END_ARRAY")))
                  (.binop "!=" (.name "token") (.field (.name "JsonToken") "END_DOCUMENT")))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.peek:com.google.gson.stream.JsonToken()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_peek_com_google_gson_stream_JsonToken__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.peek:com.google.gson.stream.JsonToken()"
  , params := ["this"]
  , body := (.seq
            (.ifte
              (.binop "==" (.field (.name "this") "stackSize") (.lit (.int 0)))
              (.ret (.field (.name "JsonToken") "END_DOCUMENT"))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign
                  "o"
                  (.call
                    "com.google.gson.internal.bind.JsonTreeReader.peekStack:java.lang.Object()"
                    []))
                (.ifte
                  (.hole "op:instanceOf")
                  (.seq
                    .skip
                    (.seq
                      (.assign "isObject" (.hole "op:instanceOf"))
                      (.seq
                        .skip
                        (.seq
                          (.assign "iterator" (.hole "op:cast"))
                          (.ifte
                            (.call "hasNext" [])
                            (.ifte
                              (.name "isObject")
                              (.ret (.field (.name "JsonToken") "NAME"))
                              (.seq
                                (.expr
                                  (.call
                                    "com.google.gson.internal.bind.JsonTreeReader.push:void(java.lang.Object)"
                                    [(.call "next" [])]))
                                (.ret
                                  (.call
                                    "com.google.gson.internal.bind.JsonTreeReader.peek:com.google.gson.stream.JsonToken()"
                                    []))))
                            (.ret
                              (.cond
                                (.name "isObject")
                                (.field (.name "JsonToken") "END_OBJECT")
                                (.field (.name "JsonToken") "END_ARRAY"))))))))
                  (.ifte
                    (.hole "op:instanceOf")
                    (.ret (.field (.name "JsonToken") "BEGIN_OBJECT"))
                    (.ifte
                      (.hole "op:instanceOf")
                      (.ret (.field (.name "JsonToken") "BEGIN_ARRAY"))
                      (.ifte
                        (.hole "op:instanceOf")
                        (.seq
                          .skip
                          (.seq
                            (.assign "primitive" (.hole "op:cast"))
                            (.ifte
                              (.call "isString" [])
                              (.ret (.field (.name "JsonToken") "STRING"))
                              (.ifte
                                (.call "isBoolean" [])
                                (.ret (.field (.name "JsonToken") "BOOLEAN"))
                                (.ifte
                                  (.call "isNumber" [])
                                  (.ret (.field (.name "JsonToken") "NUMBER"))
                                  (.hole "control:THROW"))))))
                        (.ifte
                          (.hole "op:instanceOf")
                          (.ret (.field (.name "JsonToken") "NULL"))
                          (.ifte
                            (.binop
                              "=="
                              (.name "o")
                              (.field
                                (.fnref "com.google.gson.internal.bind.JsonTreeReader")
                                "SENTINEL_CLOSED"))
                            (.hole "control:THROW")
                            (.hole "control:THROW")))))))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.peekStack:java.lang.Object()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_peekStack_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.peekStack:java.lang.Object()"
  , params := ["this"]
  , body := (.ret
            (.index
              (.field (.name "this") "stack")
              (.binop "-" (.field (.name "this") "stackSize") (.lit (.int 1))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.popStack:java.lang.Object()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_popStack_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.popStack:java.lang.Object()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "result" (.index (.field (.name "this") "stack") (.hole "op:preDecrement")))
              (.seq
                (.setIndex
                  (.field (.name "this") "stack")
                  (.field (.name "this") "stackSize")
                  (.lit .unit))
                (.ret (.name "result"))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.expect:void(com.google.gson.stream.JsonToken)`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_expect_void_com_google_gson_stream_JsonToken_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.expect:void(com.google.gson.stream.JsonToken)"
  , params := ["this", "expected"]
  , body := (.ifte
            (.binop
              "!="
              (.call
                "com.google.gson.internal.bind.JsonTreeReader.peek:com.google.gson.stream.JsonToken()"
                [])
              (.name "expected"))
            (.hole "control:THROW")
            .skip) }

/-- `com.google.gson.internal.bind.JsonTreeReader.nextName:java.lang.String(boolean)`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_nextName_java_lang_String_boolean_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.nextName:java.lang.String(boolean)"
  , params := ["this", "skipName"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.bind.JsonTreeReader.expect:void(com.google.gson.stream.JsonToken)"
                [(.field (.name "JsonToken") "NAME")]))
            (.seq
              .skip
              (.seq
                (.assign "i" (.hole "op:cast"))
                (.seq
                  .skip
                  (.seq
                    (.assign "entry" (.hole "op:cast"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "result" (.hole "op:cast"))
                        (.seq
                          (.setIndex
                            (.field (.name "this") "pathNames")
                            (.binop "-" (.field (.name "this") "stackSize") (.lit (.int 1)))
                            (.cond (.name "skipName") (.lit (.str "<skipped>")) (.name "result")))
                          (.seq
                            (.expr
                              (.call
                                "com.google.gson.internal.bind.JsonTreeReader.push:void(java.lang.Object)"
                                [(.call "getValue" [])]))
                            (.ret (.name "result"))))))))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.nextName:java.lang.String()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_nextName_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.nextName:java.lang.String()"
  , params := ["this"]
  , body := (.ret
            (.call
              "com.google.gson.internal.bind.JsonTreeReader.nextName:java.lang.String(boolean)"
              [(.lit (.bool false))])) }

/-- `com.google.gson.internal.bind.JsonTreeReader.nextString:java.lang.String()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_nextString_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.nextString:java.lang.String()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "token"
                (.call
                  "com.google.gson.internal.bind.JsonTreeReader.peek:com.google.gson.stream.JsonToken()"
                  []))
              (.seq
                (.ifte
                  (.binop
                    "&&"
                    (.binop "!=" (.name "token") (.field (.name "JsonToken") "STRING"))
                    (.binop "!=" (.name "token") (.field (.name "JsonToken") "NUMBER")))
                  (.hole "control:THROW")
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "result" (.call "getAsString" []))
                    (.seq
                      (.ifte
                        (.binop ">" (.field (.name "this") "stackSize") (.lit (.int 0)))
                        (.expr (.hole "op:postIncrement"))
                        .skip)
                      (.ret (.name "result")))))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.nextBoolean:boolean()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_nextBoolean_boolean__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.nextBoolean:boolean()"
  , params := ["this"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.bind.JsonTreeReader.expect:void(com.google.gson.stream.JsonToken)"
                [(.field (.name "JsonToken") "BOOLEAN")]))
            (.seq
              .skip
              (.seq
                (.assign "result" (.call "getAsBoolean" []))
                (.seq
                  (.ifte
                    (.binop ">" (.field (.name "this") "stackSize") (.lit (.int 0)))
                    (.expr (.hole "op:postIncrement"))
                    .skip)
                  (.ret (.name "result")))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.nextNull:void()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_nextNull_void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.nextNull:void()"
  , params := ["this"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.bind.JsonTreeReader.expect:void(com.google.gson.stream.JsonToken)"
                [(.field (.name "JsonToken") "NULL")]))
            (.seq
              (.expr
                (.call
                  "com.google.gson.internal.bind.JsonTreeReader.popStack:java.lang.Object()"
                  []))
              (.ifte
                (.binop ">" (.field (.name "this") "stackSize") (.lit (.int 0)))
                (.expr (.hole "op:postIncrement"))
                .skip))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.nextDouble:double()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_nextDouble_double__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.nextDouble:double()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "token"
                (.call
                  "com.google.gson.internal.bind.JsonTreeReader.peek:com.google.gson.stream.JsonToken()"
                  []))
              (.seq
                (.ifte
                  (.binop
                    "&&"
                    (.binop "!=" (.name "token") (.field (.name "JsonToken") "NUMBER"))
                    (.binop "!=" (.name "token") (.field (.name "JsonToken") "STRING")))
                  (.hole "control:THROW")
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "primitive" (.hole "op:cast"))
                    (.seq
                      .skip
                      (.seq
                        (.tryCatch
                          (.assign "result" (.call "getAsDouble" []))
                          "__exc"
                          (.hole "control:THROW"))
                        (.seq
                          (.ifte
                            (.binop
                              "&&"
                              (.unop "!" (.call "isLenient" []))
                              (.binop
                                "||"
                                (.call "isNaN" [(.name "result")])
                                (.call "isInfinite" [(.name "result")])))
                            (.hole "control:THROW")
                            .skip)
                          (.seq
                            (.expr
                              (.call
                                "com.google.gson.internal.bind.JsonTreeReader.popStack:java.lang.Object()"
                                []))
                            (.seq
                              (.ifte
                                (.binop ">" (.field (.name "this") "stackSize") (.lit (.int 0)))
                                (.expr (.hole "op:postIncrement"))
                                .skip)
                              (.ret (.name "result")))))))))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.nextLong:long()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_nextLong_long__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.nextLong:long()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "token"
                (.call
                  "com.google.gson.internal.bind.JsonTreeReader.peek:com.google.gson.stream.JsonToken()"
                  []))
              (.seq
                (.ifte
                  (.binop
                    "&&"
                    (.binop "!=" (.name "token") (.field (.name "JsonToken") "NUMBER"))
                    (.binop "!=" (.name "token") (.field (.name "JsonToken") "STRING")))
                  (.hole "control:THROW")
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "primitive" (.hole "op:cast"))
                    (.seq
                      (.ifte
                        (.binop "==" (.name "token") (.field (.name "JsonToken") "STRING"))
                        (.expr
                          (.call
                            "com.google.gson.internal.bind.JsonTreeReader.validateAscii:void(java.lang.String)"
                            [(.call "getAsString" [])]))
                        .skip)
                      (.seq
                        .skip
                        (.seq
                          (.tryCatch
                            (.assign "result" (.call "getAsLong" []))
                            "__exc"
                            (.hole "control:THROW"))
                          (.seq
                            (.expr
                              (.call
                                "com.google.gson.internal.bind.JsonTreeReader.popStack:java.lang.Object()"
                                []))
                            (.seq
                              (.ifte
                                (.binop ">" (.field (.name "this") "stackSize") (.lit (.int 0)))
                                (.expr (.hole "op:postIncrement"))
                                .skip)
                              (.ret (.name "result")))))))))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.nextInt:int()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_nextInt_int__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.nextInt:int()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "token"
                (.call
                  "com.google.gson.internal.bind.JsonTreeReader.peek:com.google.gson.stream.JsonToken()"
                  []))
              (.seq
                (.ifte
                  (.binop
                    "&&"
                    (.binop "!=" (.name "token") (.field (.name "JsonToken") "NUMBER"))
                    (.binop "!=" (.name "token") (.field (.name "JsonToken") "STRING")))
                  (.hole "control:THROW")
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "primitive" (.hole "op:cast"))
                    (.seq
                      (.ifte
                        (.binop "==" (.name "token") (.field (.name "JsonToken") "STRING"))
                        (.expr
                          (.call
                            "com.google.gson.internal.bind.JsonTreeReader.validateAscii:void(java.lang.String)"
                            [(.call "getAsString" [])]))
                        .skip)
                      (.seq
                        .skip
                        (.seq
                          (.tryCatch
                            (.assign "result" (.call "getAsInt" []))
                            "__exc"
                            (.hole "control:THROW"))
                          (.seq
                            (.expr
                              (.call
                                "com.google.gson.internal.bind.JsonTreeReader.popStack:java.lang.Object()"
                                []))
                            (.seq
                              (.ifte
                                (.binop ">" (.field (.name "this") "stackSize") (.lit (.int 0)))
                                (.expr (.hole "op:postIncrement"))
                                .skip)
                              (.ret (.name "result")))))))))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.nextJsonElement:com.google.gson.JsonElement()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_nextJsonElement_com_google_gson_JsonElement__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.nextJsonElement:com.google.gson.JsonElement()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "peeked"
                (.call
                  "com.google.gson.internal.bind.JsonTreeReader.peek:com.google.gson.stream.JsonToken()"
                  []))
              (.seq
                (.ifte
                  (.binop
                    "||"
                    (.binop
                      "||"
                      (.binop
                        "||"
                        (.binop "==" (.name "peeked") (.field (.name "JsonToken") "NAME"))
                        (.binop "==" (.name "peeked") (.field (.name "JsonToken") "END_ARRAY")))
                      (.binop "==" (.name "peeked") (.field (.name "JsonToken") "END_OBJECT")))
                    (.binop "==" (.name "peeked") (.field (.name "JsonToken") "END_DOCUMENT")))
                  (.hole "control:THROW")
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "element" (.hole "op:cast"))
                    (.seq
                      (.expr
                        (.call "com.google.gson.internal.bind.JsonTreeReader.skipValue:void()" []))
                      (.ret (.name "element")))))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.close:void()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_close_void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.close:void()"
  , params := ["this"]
  , body := (.seq
            (.setField (.name "this") "stack" (.hole "op:arrayInitializer"))
            (.setField (.name "this") "stackSize" (.lit (.int 1)))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.skipValue:void()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_skipValue_void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.skipValue:void()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "peeked"
                (.call
                  "com.google.gson.internal.bind.JsonTreeReader.peek:com.google.gson.stream.JsonToken()"
                  []))
              (.hole "control:SWITCH"))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.toString:java.lang.String()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_toString_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.toString:java.lang.String()"
  , params := ["this"]
  , body := (.ret
            (.binop
              "+"
              (.call "getSimpleName" [])
              (.call
                "com.google.gson.internal.bind.JsonTreeReader.locationString:java.lang.String()"
                []))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.promoteNameToValue:void()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_promoteNameToValue_void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.promoteNameToValue:void()"
  , params := ["this"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.bind.JsonTreeReader.expect:void(com.google.gson.stream.JsonToken)"
                [(.field (.name "JsonToken") "NAME")]))
            (.seq
              .skip
              (.seq
                (.assign "i" (.hole "op:cast"))
                (.seq
                  .skip
                  (.seq
                    (.assign "entry" (.hole "op:cast"))
                    (.seq
                      (.expr
                        (.call
                          "com.google.gson.internal.bind.JsonTreeReader.push:void(java.lang.Object)"
                          [(.call "getValue" [])]))
                      (.expr (.call "push" [(.hole "expr:BLOCK-impure")])))))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.push:void(java.lang.Object)`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_push_void_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.push:void(java.lang.Object)"
  , params := ["this", "newTop"]
  , body := (.seq
            (.ifte
              (.binop "==" (.field (.name "this") "stackSize") (.hole "op:sizeOf"))
              (.seq
                .skip
                (.seq
                  (.assign
                    "newLength"
                    (.binop "*" (.field (.name "this") "stackSize") (.lit (.int 2))))
                  (.seq
                    (.setField
                      (.name "this")
                      "stack"
                      (.call "copyOf" [(.field (.name "this") "stack"), (.name "newLength")]))
                    (.seq
                      (.setField
                        (.name "this")
                        "pathIndices"
                        (.call
                          "copyOf"
                          [(.field (.name "this") "pathIndices"), (.name "newLength")]))
                      (.setField
                        (.name "this")
                        "pathNames"
                        (.call "copyOf" [(.field (.name "this") "pathNames"), (.name "newLength")]))))))
              .skip)
            (.setIndex (.field (.name "this") "stack") (.hole "op:postIncrement") (.name "newTop"))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.getPath:java.lang.String(boolean)`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_getPath_java_lang_String_boolean_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.getPath:java.lang.String(boolean)"
  , params := ["this", "usePreviousPath"]
  , body := (.seq
            .skip
            (.seq
              (.assign "result" (.call "append" [(.lit (.str "$"))]))
              (.seq (.hole "control:FOR") (.ret (.call "toString" []))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.getPath:java.lang.String()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_getPath_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.getPath:java.lang.String()"
  , params := ["this"]
  , body := (.ret
            (.call
              "com.google.gson.internal.bind.JsonTreeReader.getPath:java.lang.String(boolean)"
              [(.lit (.bool false))])) }

/-- `com.google.gson.internal.bind.JsonTreeReader.getPreviousPath:java.lang.String()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_getPreviousPath_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.getPreviousPath:java.lang.String()"
  , params := ["this"]
  , body := (.ret
            (.call
              "com.google.gson.internal.bind.JsonTreeReader.getPath:java.lang.String(boolean)"
              [(.lit (.bool true))])) }

/-- `com.google.gson.internal.bind.JsonTreeReader.locationString:java.lang.String()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_locationString_java_lang_String__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.locationString:java.lang.String()"
  , params := ["this"]
  , body := (.ret
            (.binop
              "+"
              (.lit (.str " at path "))
              (.call "com.google.gson.internal.bind.JsonTreeReader.getPath:java.lang.String()" []))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.isAllAscii:boolean(java.lang.String)`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_isAllAscii_boolean_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.isAllAscii:boolean(java.lang.String)"
  , params := ["s"]
  , body := (.seq (.hole "control:FOR") (.ret (.lit (.bool true)))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.validateAscii:void(java.lang.String)`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_validateAscii_void_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.validateAscii:void(java.lang.String)"
  , params := ["this", "s"]
  , body := (.ifte
            (.unop
              "!"
              (.call
                "com.google.gson.internal.bind.JsonTreeReader.isAllAscii:boolean(java.lang.String)"
                [(.name "s")]))
            (.hole "control:THROW")
            .skip) }

/-- `com.google.gson.internal.bind.JsonTreeReader.numberFormatException:java.lang.NumberFormatException(java.lang.String,java.lang.NumberFormatException)`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_numberFormatException_java_lang_NumberFormatException_java_lang_String_ja : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.numberFormatException:java.lang.NumberFormatException(java.lang.String,java.lang.NumberFormatException)"
  , params := ["this", "message", "cause"]
  , body := (.seq
            .skip
            (.seq
              (.assign "exception" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "<init>"
                    [ (.binop
                        "+"
                        (.name "message")
                        (.call
                          "com.google.gson.internal.bind.JsonTreeReader.locationString:java.lang.String()"
                          [])) ]))
                (.seq (.expr (.call "initCause" [(.name "cause")])) (.ret (.name "exception")))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_JsonTreeReader__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.bind.JsonTreeReader")
              "UNREADABLE_READER"
              (.hole "op:alloc"))
            (.seq
              (.expr
                (.mcall
                  (.fnref "com.google.gson.internal.bind.JsonTreeReader")
                  "UNREADABLE_READER"
                  []))
              (.seq
                (.setField
                  (.fnref "com.google.gson.internal.bind.JsonTreeReader")
                  "SENTINEL_CLOSED"
                  (.hole "op:alloc"))
                (.expr
                  (.mcall
                    (.fnref "com.google.gson.internal.bind.JsonTreeReader")
                    "SENTINEL_CLOSED"
                    []))))) }

/-- `com.google.gson.internal.bind.JsonTreeReader.UNREADABLE_READER.Reader$0.read:int(char[],int,int)`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_UNREADABLE_READER_Reader_0_read_int_char___int_int_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.UNREADABLE_READER.Reader$0.read:int(char[],int,int)"
  , params := ["this", "buffer", "offset", "count"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.bind.JsonTreeReader.UNREADABLE_READER.Reader$0.close:void()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_UNREADABLE_READER_Reader_0_close_void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.UNREADABLE_READER.Reader$0.close:void()"
  , params := ["this"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.bind.JsonTreeReader.UNREADABLE_READER.Reader$0.<init>:void()`  (from `internal/bind/JsonTreeReader.java`) -/
def f_com_google_gson_internal_bind_JsonTreeReader_UNREADABLE_READER_Reader_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeReader.UNREADABLE_READER.Reader$0.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JsonTreeWriter.<init>:void()`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.<init>:void()"
  , params := ["this"]
  , body := (.seq
            (.setField (.name "this") "stack" (.hole "op:alloc"))
            (.seq
              (.expr (.mcall (.name "this") "stack" []))
              (.seq
                (.setField (.name "this") "product" (.field (.name "JsonNull") "INSTANCE"))
                (.expr
                  (.call
                    "<init>"
                    [ (.field
                        (.fnref "com.google.gson.internal.bind.JsonTreeWriter")
                        "UNWRITABLE_WRITER") ]))))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.get:com.google.gson.JsonElement()`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_get_com_google_gson_JsonElement__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.get:com.google.gson.JsonElement()"
  , params := ["this"]
  , body := (.seq
            (.ifte (.unop "!" (.mcall (.name "this") "stack" [])) (.hole "control:THROW") .skip)
            (.ret (.field (.name "this") "product"))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.peek:com.google.gson.JsonElement()`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_peek_com_google_gson_JsonElement__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.peek:com.google.gson.JsonElement()"
  , params := ["this"]
  , body := (.ret
            (.mcall
              (.name "this")
              "stack"
              [(.binop "-" (.mcall (.name "this") "stack" []) (.lit (.int 1)))])) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.put:void(com.google.gson.JsonElement)`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_put_void_com_google_gson_JsonElement_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.put:void(com.google.gson.JsonElement)"
  , params := ["this", "value"]
  , body := (.ifte
            (.binop "!=" (.field (.name "this") "pendingName") (.lit .unit))
            (.seq
              (.ifte
                (.binop "||" (.unop "!" (.call "isJsonNull" [])) (.call "getSerializeNulls" []))
                (.seq
                  .skip
                  (.seq
                    (.assign "object" (.hole "op:cast"))
                    (.expr (.call "add" [(.field (.name "this") "pendingName"), (.name "value")]))))
                .skip)
              (.setField (.name "this") "pendingName" (.lit .unit)))
            (.ifte
              (.mcall (.name "this") "stack" [])
              (.setField (.name "this") "product" (.name "value"))
              (.seq
                .skip
                (.seq
                  (.assign
                    "element"
                    (.call
                      "com.google.gson.internal.bind.JsonTreeWriter.peek:com.google.gson.JsonElement()"
                      []))
                  (.ifte
                    (.hole "op:instanceOf")
                    (.expr (.call "add" [(.name "value")]))
                    (.hole "control:THROW")))))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.beginArray:com.google.gson.stream.JsonWriter()`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_beginArray_com_google_gson_stream_JsonWriter__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.beginArray:com.google.gson.stream.JsonWriter()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "array" (.hole "op:alloc"))
              (.seq
                (.expr (.call "<init>" []))
                (.seq
                  (.expr (.call "put" [(.name "array")]))
                  (.seq
                    (.expr (.mcall (.name "this") "stack" [(.name "array")]))
                    (.ret (.name "this"))))))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.endArray:com.google.gson.stream.JsonWriter()`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_endArray_com_google_gson_stream_JsonWriter__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.endArray:com.google.gson.stream.JsonWriter()"
  , params := ["this"]
  , body := (.seq
            (.ifte
              (.binop
                "||"
                (.mcall (.name "this") "stack" [])
                (.binop "!=" (.field (.name "this") "pendingName") (.lit .unit)))
              (.hole "control:THROW")
              .skip)
            (.seq
              .skip
              (.seq
                (.assign
                  "element"
                  (.call
                    "com.google.gson.internal.bind.JsonTreeWriter.peek:com.google.gson.JsonElement()"
                    []))
                (.seq
                  (.ifte
                    (.hole "op:instanceOf")
                    (.seq
                      (.expr
                        (.mcall
                          (.name "this")
                          "stack"
                          [(.binop "-" (.mcall (.name "this") "stack" []) (.lit (.int 1)))]))
                      (.ret (.name "this")))
                    .skip)
                  (.hole "control:THROW"))))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.beginObject:com.google.gson.stream.JsonWriter()`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_beginObject_com_google_gson_stream_JsonWriter__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.beginObject:com.google.gson.stream.JsonWriter()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "object" (.hole "op:alloc"))
              (.seq
                (.expr (.call "<init>" []))
                (.seq
                  (.expr (.call "put" [(.name "object")]))
                  (.seq
                    (.expr (.mcall (.name "this") "stack" [(.name "object")]))
                    (.ret (.name "this"))))))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.endObject:com.google.gson.stream.JsonWriter()`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_endObject_com_google_gson_stream_JsonWriter__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.endObject:com.google.gson.stream.JsonWriter()"
  , params := ["this"]
  , body := (.seq
            (.ifte
              (.binop
                "||"
                (.mcall (.name "this") "stack" [])
                (.binop "!=" (.field (.name "this") "pendingName") (.lit .unit)))
              (.hole "control:THROW")
              .skip)
            (.seq
              .skip
              (.seq
                (.assign
                  "element"
                  (.call
                    "com.google.gson.internal.bind.JsonTreeWriter.peek:com.google.gson.JsonElement()"
                    []))
                (.seq
                  (.ifte
                    (.hole "op:instanceOf")
                    (.seq
                      (.expr
                        (.mcall
                          (.name "this")
                          "stack"
                          [(.binop "-" (.mcall (.name "this") "stack" []) (.lit (.int 1)))]))
                      (.ret (.name "this")))
                    .skip)
                  (.hole "control:THROW"))))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.name:com.google.gson.stream.JsonWriter(java.lang.String)`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_name_com_google_gson_stream_JsonWriter_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.name:com.google.gson.stream.JsonWriter(java.lang.String)"
  , params := ["this", "name"]
  , body := (.seq
            (.expr (.call "requireNonNull" [(.name "name"), (.lit (.str "name == null"))]))
            (.seq
              (.ifte
                (.binop
                  "||"
                  (.mcall (.name "this") "stack" [])
                  (.binop "!=" (.field (.name "this") "pendingName") (.lit .unit)))
                (.hole "control:THROW")
                .skip)
              (.seq
                .skip
                (.seq
                  (.assign
                    "element"
                    (.call
                      "com.google.gson.internal.bind.JsonTreeWriter.peek:com.google.gson.JsonElement()"
                      []))
                  (.seq
                    (.ifte
                      (.hole "op:instanceOf")
                      (.seq
                        (.setField (.name "this") "pendingName" (.name "name"))
                        (.ret (.name "this")))
                      .skip)
                    (.hole "control:THROW")))))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(java.lang.String)`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(java.lang.String)"
  , params := ["this", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "value") (.lit .unit))
              (.ret
                (.call
                  "com.google.gson.internal.bind.JsonTreeWriter.nullValue:com.google.gson.stream.JsonWriter()"
                  []))
              .skip)
            (.seq (.expr (.call "put" [(.hole "expr:BLOCK-impure")])) (.ret (.name "this")))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(boolean)`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_boolean_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(boolean)"
  , params := ["this", "value"]
  , body := (.seq (.expr (.call "put" [(.hole "expr:BLOCK-impure")])) (.ret (.name "this"))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(java.lang.Boolean)`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_java_lang_Boolean_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(java.lang.Boolean)"
  , params := ["this", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "value") (.lit .unit))
              (.ret
                (.call
                  "com.google.gson.internal.bind.JsonTreeWriter.nullValue:com.google.gson.stream.JsonWriter()"
                  []))
              .skip)
            (.seq (.expr (.call "put" [(.hole "expr:BLOCK-impure")])) (.ret (.name "this")))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(float)`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_float_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(float)"
  , params := ["this", "value"]
  , body := (.seq
            (.ifte
              (.binop
                "&&"
                (.unop "!" (.call "isLenient" []))
                (.binop
                  "||"
                  (.call "isNaN" [(.name "value")])
                  (.call "isInfinite" [(.name "value")])))
              (.hole "control:THROW")
              .skip)
            (.seq (.expr (.call "put" [(.hole "expr:BLOCK-impure")])) (.ret (.name "this")))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(double)`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_double_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(double)"
  , params := ["this", "value"]
  , body := (.seq
            (.ifte
              (.binop
                "&&"
                (.unop "!" (.call "isLenient" []))
                (.binop
                  "||"
                  (.call "isNaN" [(.name "value")])
                  (.call "isInfinite" [(.name "value")])))
              (.hole "control:THROW")
              .skip)
            (.seq (.expr (.call "put" [(.hole "expr:BLOCK-impure")])) (.ret (.name "this")))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(long)`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_long_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(long)"
  , params := ["this", "value"]
  , body := (.seq (.expr (.call "put" [(.hole "expr:BLOCK-impure")])) (.ret (.name "this"))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(java.lang.Number)`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_java_lang_Number_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.value:com.google.gson.stream.JsonWriter(java.lang.Number)"
  , params := ["this", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "value") (.lit .unit))
              (.ret
                (.call
                  "com.google.gson.internal.bind.JsonTreeWriter.nullValue:com.google.gson.stream.JsonWriter()"
                  []))
              .skip)
            (.seq
              (.ifte
                (.unop "!" (.call "isLenient" []))
                (.seq
                  .skip
                  (.seq
                    (.assign "d" (.call "doubleValue" []))
                    (.ifte
                      (.binop "||" (.call "isNaN" [(.name "d")]) (.call "isInfinite" [(.name "d")]))
                      (.hole "control:THROW")
                      .skip)))
                .skip)
              (.seq (.expr (.call "put" [(.hole "expr:BLOCK-impure")])) (.ret (.name "this"))))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.nullValue:com.google.gson.stream.JsonWriter()`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_nullValue_com_google_gson_stream_JsonWriter__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.nullValue:com.google.gson.stream.JsonWriter()"
  , params := ["this"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.bind.JsonTreeWriter.put:void(com.google.gson.JsonElement)"
                [(.field (.name "JsonNull") "INSTANCE")]))
            (.ret (.name "this"))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.jsonValue:com.google.gson.stream.JsonWriter(java.lang.String)`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_jsonValue_com_google_gson_stream_JsonWriter_java_lang_String_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.jsonValue:com.google.gson.stream.JsonWriter(java.lang.String)"
  , params := ["this", "value"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.bind.JsonTreeWriter.flush:void()`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_flush_void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.flush:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.JsonTreeWriter.close:void()`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_close_void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.close:void()"
  , params := ["this"]
  , body := (.seq
            (.ifte (.unop "!" (.mcall (.name "this") "stack" [])) (.hole "control:THROW") .skip)
            (.expr
              (.mcall
                (.name "this")
                "stack"
                [(.field (.fnref "com.google.gson.internal.bind.JsonTreeWriter") "SENTINEL_CLOSED")]))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.bind.JsonTreeWriter")
              "UNWRITABLE_WRITER"
              (.hole "op:alloc"))
            (.seq
              (.expr
                (.mcall
                  (.fnref "com.google.gson.internal.bind.JsonTreeWriter")
                  "UNWRITABLE_WRITER"
                  []))
              (.seq
                (.setField
                  (.fnref "com.google.gson.internal.bind.JsonTreeWriter")
                  "SENTINEL_CLOSED"
                  (.hole "op:alloc"))
                (.expr
                  (.mcall
                    (.fnref "com.google.gson.internal.bind.JsonTreeWriter")
                    "SENTINEL_CLOSED"
                    [(.lit (.str "closed"))]))))) }

/-- `com.google.gson.internal.bind.JsonTreeWriter.UNWRITABLE_WRITER.Writer$0.write:void(char[],int,int)`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_UNWRITABLE_WRITER_Writer_0_write_void_char___int_int_ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.UNWRITABLE_WRITER.Writer$0.write:void(char[],int,int)"
  , params := ["this", "buffer", "offset", "counter"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.bind.JsonTreeWriter.UNWRITABLE_WRITER.Writer$0.flush:void()`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_UNWRITABLE_WRITER_Writer_0_flush_void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.UNWRITABLE_WRITER.Writer$0.flush:void()"
  , params := ["this"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.bind.JsonTreeWriter.UNWRITABLE_WRITER.Writer$0.close:void()`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_UNWRITABLE_WRITER_Writer_0_close_void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.UNWRITABLE_WRITER.Writer$0.close:void()"
  , params := ["this"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.bind.JsonTreeWriter.UNWRITABLE_WRITER.Writer$0.<init>:void()`  (from `internal/bind/JsonTreeWriter.java`) -/
def f_com_google_gson_internal_bind_JsonTreeWriter_UNWRITABLE_WRITER_Writer_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.JsonTreeWriter.UNWRITABLE_WRITER.Writer$0.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.MapTypeAdapterFactory.<init>:void(com.google.gson.internal.ConstructorConstructor,boolean)`  (from `internal/bind/MapTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_MapTypeAdapterFactory__init__void_com_google_gson_internal_ConstructorConstructor_boolea : Func :=
  { name := "com.google.gson.internal.bind.MapTypeAdapterFactory.<init>:void(com.google.gson.internal.ConstructorConstructor,boolean)"
  , params := ["this", "constructorConstructor", "complexMapKeySerialization"]
  , body := (.seq
            (.setField (.name "this") "constructorConstructor" (.name "constructorConstructor"))
            (.setField
              (.name "this")
              "complexMapKeySerialization"
              (.name "complexMapKeySerialization"))) }

/-- `com.google.gson.internal.bind.MapTypeAdapterFactory.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/MapTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_MapTypeAdapterFactory_create_com_google_gson_TypeAdapter_com_google_gson_Gson_com_google : Func :=
  { name := "com.google.gson.internal.bind.MapTypeAdapterFactory.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.seq
            .skip
            (.seq
              (.assign "type" (.call "getType" []))
              (.seq
                .skip
                (.seq
                  (.assign "rawType" (.call "getRawType" []))
                  (.seq
                    (.ifte
                      (.unop "!" (.mcall (.name "Map") "class" [(.name "rawType")]))
                      (.ret (.lit .unit))
                      .skip)
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "keyAndValueTypes"
                          (.call
                            "com.google.gson.internal.GsonTypes.getMapKeyAndValueTypes:java.lang.reflect.Type[](java.lang.reflect.Type,java.lang.Class)"
                            [(.name "type"), (.name "rawType")]))
                        (.seq
                          .skip
                          (.seq
                            (.assign "keyType" (.index (.name "keyAndValueTypes") (.lit (.int 0))))
                            (.seq
                              .skip
                              (.seq
                                (.assign
                                  "valueType"
                                  (.index (.name "keyAndValueTypes") (.lit (.int 1))))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign
                                      "keyAdapter"
                                      (.call
                                        "com.google.gson.internal.bind.MapTypeAdapterFactory.getKeyAdapter:com.google.gson.TypeAdapter(com.google.gson.Gson,java.lang.reflect.Type)"
                                        [(.name "gson"), (.name "keyType")]))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign "wrappedKeyAdapter" (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "<init>"
                                        [(.name "gson"), (.name "keyAdapter"), (.name "keyType")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "valueAdapter"
                                        (.call "getAdapter" [(.call "get" [(.name "valueType")])]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "wrappedValueAdapter" (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "<init>"
                                        [ (.name "gson")
                                        , (.name "valueAdapter")
                                        , (.name "valueType") ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "allowUnsafe" (.lit (.bool false)))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "constructor"
                                        (.mcall
                                        (.name "this")
                                        "constructorConstructor"
                                        [(.name "typeToken"), (.name "allowUnsafe")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "result" (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "<init>"
                                        [ (.name "wrappedKeyAdapter")
                                        , (.name "wrappedValueAdapter")
                                        , (.name "constructor") ]))
                                        (.ret (.name "result")))))))))))))))))))))))))))))) }

/-- `com.google.gson.internal.bind.MapTypeAdapterFactory.getKeyAdapter:com.google.gson.TypeAdapter(com.google.gson.Gson,java.lang.reflect.Type)`  (from `internal/bind/MapTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_MapTypeAdapterFactory_getKeyAdapter_com_google_gson_TypeAdapter_com_google_gson_Gson_jav : Func :=
  { name := "com.google.gson.internal.bind.MapTypeAdapterFactory.getKeyAdapter:com.google.gson.TypeAdapter(com.google.gson.Gson,java.lang.reflect.Type)"
  , params := ["this", "context", "keyType"]
  , body := (.ret
            (.cond
              (.binop
                "||"
                (.binop "==" (.name "keyType") (.field (.name "boolean") "class"))
                (.binop "==" (.name "keyType") (.field (.name "Boolean") "class")))
              (.field (.name "TypeAdapters") "BOOLEAN_AS_STRING")
              (.call "getAdapter" [(.call "get" [(.name "keyType")])]))) }

/-- `com.google.gson.internal.bind.MapTypeAdapterFactory$Adapter.<init>:void(com.google.gson.TypeAdapter,com.google.gson.TypeAdapter,com.google.gson.internal.ObjectConstructor)`  (from `internal/bind/MapTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_MapTypeAdapterFactory_Adapter__init__void_com_google_gson_TypeAdapter_com_google_gson_Ty : Func :=
  { name := "com.google.gson.internal.bind.MapTypeAdapterFactory$Adapter.<init>:void(com.google.gson.TypeAdapter,com.google.gson.TypeAdapter,com.google.gson.internal.ObjectConstructor)"
  , params := ["this", "keyTypeAdapter", "valueTypeAdapter", "constructor", "outerClass"]
  , body := (.seq
            (.setField (.name "this") "outerClass" (.name "outerClass"))
            (.seq
              (.setField (.name "this") "keyTypeAdapter" (.name "keyTypeAdapter"))
              (.seq
                (.setField (.name "this") "valueTypeAdapter" (.name "valueTypeAdapter"))
                (.setField (.name "this") "constructor" (.name "constructor"))))) }

/-- `com.google.gson.internal.bind.MapTypeAdapterFactory$Adapter.read:java.util.Map(com.google.gson.stream.JsonReader)`  (from `internal/bind/MapTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_MapTypeAdapterFactory_Adapter_read_java_util_Map_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.bind.MapTypeAdapterFactory$Adapter.read:java.util.Map(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              (.assign "peek" (.call "peek" []))
              (.seq
                (.ifte
                  (.binop "==" (.name "peek") (.field (.name "JsonToken") "NULL"))
                  (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "map" (.mcall (.name "this") "constructor" []))
                    (.seq
                      (.ifte
                        (.binop "==" (.name "peek") (.field (.name "JsonToken") "BEGIN_ARRAY"))
                        (.seq
                          (.expr (.call "beginArray" []))
                          (.seq
                            (.loop
                              (.call "hasNext" [])
                              (.seq
                                (.expr (.call "beginArray" []))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign
                                      "key"
                                      (.mcall (.name "this") "keyTypeAdapter" [(.name "in")]))
                                    (.seq
                                      (.ifte
                                        (.call "containsKey" [(.name "key")])
                                        (.hole "control:THROW")
                                        .skip)
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "value"
                                        (.mcall (.name "this") "valueTypeAdapter" [(.name "in")]))
                                        (.seq
                                        (.expr (.call "put" [(.name "key"), (.name "value")]))
                                        (.expr (.call "endArray" []))))))))))
                            (.expr (.call "endArray" []))))
                        (.seq
                          (.expr (.call "beginObject" []))
                          (.seq
                            (.loop
                              (.call "hasNext" [])
                              (.seq
                                (.expr
                                  (.mcall
                                    (.name "JsonReaderInternalAccess")
                                    "INSTANCE"
                                    [(.name "in")]))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign
                                      "key"
                                      (.mcall (.name "this") "keyTypeAdapter" [(.name "in")]))
                                    (.seq
                                      (.ifte
                                        (.call "containsKey" [(.name "key")])
                                        (.hole "control:THROW")
                                        .skip)
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "value"
                                        (.mcall (.name "this") "valueTypeAdapter" [(.name "in")]))
                                        (.expr (.call "put" [(.name "key"), (.name "value")])))))))))
                            (.expr (.call "endObject" [])))))
                      (.ret (.name "map")))))))) }

/-- `com.google.gson.internal.bind.MapTypeAdapterFactory$Adapter.write:void(com.google.gson.stream.JsonWriter,java.util.Map)`  (from `internal/bind/MapTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_MapTypeAdapterFactory_Adapter_write_void_com_google_gson_stream_JsonWriter_java_util_Map : Func :=
  { name := "com.google.gson.internal.bind.MapTypeAdapterFactory$Adapter.write:void(com.google.gson.stream.JsonWriter,java.util.Map)"
  , params := ["this", "out", "map"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "map") (.lit .unit))
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              (.ifte
                (.unop
                  "!"
                  (.field (.field (.name "this") "outerClass") "complexMapKeySerialization"))
                (.seq
                  (.expr (.call "beginObject" []))
                  (.seq
                    .skip
                    (.seq
                      (.assign "$iterLocal0" (.call "iterator" []))
                      (.seq
                        (.loop
                          (.call "hasNext" [])
                          (.seq
                            .skip
                            (.seq
                              (.assign "entry" (.call "next" []))
                              (.seq
                                (.expr (.call "name" [(.call "valueOf" [(.call "getKey" [])])]))
                                (.expr
                                  (.mcall
                                    (.name "this")
                                    "valueTypeAdapter"
                                    [(.name "out"), (.call "getValue" [])]))))))
                        (.seq (.expr (.call "endObject" [])) (.ret (.lit .unit)))))))
                .skip)
              (.seq
                .skip
                (.seq
                  (.assign "hasComplexKeys" (.lit (.bool false)))
                  (.seq
                    .skip
                    (.seq
                      (.assign "keys" (.hole "op:alloc"))
                      (.seq
                        (.expr (.call "<init>" [(.call "size" [])]))
                        (.seq
                          .skip
                          (.seq
                            (.assign "values" (.hole "op:alloc"))
                            (.seq
                              (.expr (.call "<init>" [(.call "size" [])]))
                              (.seq
                                .skip
                                (.seq
                                  (.assign "$iterLocal1" (.call "iterator" []))
                                  (.seq
                                    (.loop
                                      (.call "hasNext" [])
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign "entry" (.call "next" []))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "keyElement"
                                        (.mcall
                                        (.name "this")
                                        "keyTypeAdapter"
                                        [(.call "getKey" [])]))
                                        (.seq
                                        (.expr (.call "add" [(.name "keyElement")]))
                                        (.seq
                                        (.expr (.call "add" [(.call "getValue" [])]))
                                        (.expr
                                        (.call
                                        "<operators>.assignmentOr"
                                        [ (.name "hasComplexKeys")
                                        , (.binop
                                        "||"
                                        (.call "isJsonArray" [])
                                        (.call "isJsonObject" [])) ])))))))))
                                    (.ifte
                                      (.name "hasComplexKeys")
                                      (.seq
                                        (.expr (.call "beginArray" []))
                                        (.seq (.hole "control:FOR") (.expr (.call "endArray" []))))
                                      (.seq
                                        (.expr (.call "beginObject" []))
                                        (.seq (.hole "control:FOR") (.expr (.call "endObject" [])))))))))))))))))) }

/-- `com.google.gson.internal.bind.MapTypeAdapterFactory$Adapter.keyToString:java.lang.String(com.google.gson.JsonElement)`  (from `internal/bind/MapTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_MapTypeAdapterFactory_Adapter_keyToString_java_lang_String_com_google_gson_JsonElement_ : Func :=
  { name := "com.google.gson.internal.bind.MapTypeAdapterFactory$Adapter.keyToString:java.lang.String(com.google.gson.JsonElement)"
  , params := ["this", "keyElement"]
  , body := (.ifte
            (.call "isJsonPrimitive" [])
            (.seq
              .skip
              (.seq
                (.assign "primitive" (.call "getAsJsonPrimitive" []))
                (.ifte
                  (.call "isNumber" [])
                  (.ret (.call "valueOf" [(.call "getAsNumber" [])]))
                  (.ifte
                    (.call "isBoolean" [])
                    (.ret (.call "toString" [(.call "getAsBoolean" [])]))
                    (.ifte
                      (.call "isString" [])
                      (.ret (.call "getAsString" []))
                      (.hole "control:THROW"))))))
            (.ifte (.call "isJsonNull" []) (.ret (.lit (.str "null"))) (.hole "control:THROW"))) }

/-- `com.google.gson.internal.bind.NumberTypeAdapter.<init>:void(com.google.gson.ToNumberStrategy)`  (from `internal/bind/NumberTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_NumberTypeAdapter__init__void_com_google_gson_ToNumberStrategy_ : Func :=
  { name := "com.google.gson.internal.bind.NumberTypeAdapter.<init>:void(com.google.gson.ToNumberStrategy)"
  , params := ["this", "toNumberStrategy"]
  , body := (.setField (.name "this") "toNumberStrategy" (.name "toNumberStrategy")) }

/-- `com.google.gson.internal.bind.NumberTypeAdapter.newFactory:com.google.gson.TypeAdapterFactory(com.google.gson.ToNumberStrategy)`  (from `internal/bind/NumberTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_NumberTypeAdapter_newFactory_com_google_gson_TypeAdapterFactory_com_google_gson_ToNumber : Func :=
  { name := "com.google.gson.internal.bind.NumberTypeAdapter.newFactory:com.google.gson.TypeAdapterFactory(com.google.gson.ToNumberStrategy)"
  , params := ["toNumberStrategy"]
  , body := (.seq
            .skip
            (.seq
              (.assign "adapter" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.bind.NumberTypeAdapter.<init>:void(com.google.gson.ToNumberStrategy)"
                    [(.name "toNumberStrategy")]))
                (.seq
                  .skip
                  (.seq
                    (.assign "$obj0" (.hole "op:alloc"))
                    (.seq
                      (.expr
                        (.call
                          "com.google.gson.internal.bind.NumberTypeAdapter.newFactory.TypeAdapterFactory$0.<init>:void()"
                          [(.name "adapter")]))
                      (.ret (.name "$obj0")))))))) }

/-- `com.google.gson.internal.bind.NumberTypeAdapter.getFactory:com.google.gson.TypeAdapterFactory(com.google.gson.ToNumberStrategy)`  (from `internal/bind/NumberTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_NumberTypeAdapter_getFactory_com_google_gson_TypeAdapterFactory_com_google_gson_ToNumber : Func :=
  { name := "com.google.gson.internal.bind.NumberTypeAdapter.getFactory:com.google.gson.TypeAdapterFactory(com.google.gson.ToNumberStrategy)"
  , params := ["toNumberStrategy"]
  , body := (.ifte
            (.binop
              "=="
              (.name "toNumberStrategy")
              (.field (.name "ToNumberPolicy") "LAZILY_PARSED_NUMBER"))
            (.ret
              (.field
                (.fnref "com.google.gson.internal.bind.NumberTypeAdapter")
                "LAZILY_PARSED_NUMBER_FACTORY"))
            (.ret
              (.call
                "com.google.gson.internal.bind.NumberTypeAdapter.newFactory:com.google.gson.TypeAdapterFactory(com.google.gson.ToNumberStrategy)"
                [(.name "toNumberStrategy")]))) }

/-- `com.google.gson.internal.bind.NumberTypeAdapter.read:java.lang.Number(com.google.gson.stream.JsonReader)`  (from `internal/bind/NumberTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_NumberTypeAdapter_read_java_lang_Number_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.bind.NumberTypeAdapter.read:java.lang.Number(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq .skip (.seq (.assign "jsonToken" (.call "peek" [])) (.hole "control:SWITCH"))) }

/-- `com.google.gson.internal.bind.NumberTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Number)`  (from `internal/bind/NumberTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_NumberTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Number_ : Func :=
  { name := "com.google.gson.internal.bind.NumberTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Number)"
  , params := ["this", "out", "value"]
  , body := (.expr (.call "value" [(.name "value")])) }

/-- `com.google.gson.internal.bind.NumberTypeAdapter.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_NumberTypeAdapter__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.NumberTypeAdapter.<clinit>:void()"
  , params := []
  , body := (.setField
            (.fnref "com.google.gson.internal.bind.NumberTypeAdapter")
            "LAZILY_PARSED_NUMBER_FACTORY"
            (.call
              "com.google.gson.internal.bind.NumberTypeAdapter.newFactory:com.google.gson.TypeAdapterFactory(com.google.gson.ToNumberStrategy)"
              [(.field (.name "ToNumberPolicy") "LAZILY_PARSED_NUMBER")])) }

/-- `com.google.gson.internal.bind.NumberTypeAdapter.newFactory.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/NumberTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_NumberTypeAdapter_newFactory_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com : Func :=
  { name := "com.google.gson.internal.bind.NumberTypeAdapter.newFactory.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "type"]
  , body := (.ret
            (.cond
              (.binop "==" (.call "getRawType" []) (.field (.name "Number") "class"))
              (.hole "op:cast")
              (.lit .unit))) }

/-- `com.google.gson.internal.bind.NumberTypeAdapter.newFactory.TypeAdapterFactory$0.<init>:void()`  (from `internal/bind/NumberTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_NumberTypeAdapter_newFactory_TypeAdapterFactory_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.NumberTypeAdapter.newFactory.TypeAdapterFactory$0.<init>:void()"
  , params := ["this", "adapter"]
  , body := (.setField (.name "this") "adapter" (.name "adapter")) }

/-- `com.google.gson.internal.bind.ObjectTypeAdapter.<init>:void(com.google.gson.Gson,com.google.gson.ToNumberStrategy)`  (from `internal/bind/ObjectTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ObjectTypeAdapter__init__void_com_google_gson_Gson_com_google_gson_ToNumberStrategy_ : Func :=
  { name := "com.google.gson.internal.bind.ObjectTypeAdapter.<init>:void(com.google.gson.Gson,com.google.gson.ToNumberStrategy)"
  , params := ["this", "gson", "toNumberStrategy"]
  , body := (.seq
            (.setField (.name "this") "gson" (.name "gson"))
            (.setField (.name "this") "toNumberStrategy" (.name "toNumberStrategy"))) }

/-- `com.google.gson.internal.bind.ObjectTypeAdapter.newFactory:com.google.gson.TypeAdapterFactory(com.google.gson.ToNumberStrategy)`  (from `internal/bind/ObjectTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ObjectTypeAdapter_newFactory_com_google_gson_TypeAdapterFactory_com_google_gson_ToNumber : Func :=
  { name := "com.google.gson.internal.bind.ObjectTypeAdapter.newFactory:com.google.gson.TypeAdapterFactory(com.google.gson.ToNumberStrategy)"
  , params := ["toNumberStrategy"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj0" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.bind.ObjectTypeAdapter.newFactory.TypeAdapterFactory$0.<init>:void()"
                    [(.name "toNumberStrategy")]))
                (.ret (.name "$obj0"))))) }

/-- `com.google.gson.internal.bind.ObjectTypeAdapter.getFactory:com.google.gson.TypeAdapterFactory(com.google.gson.ToNumberStrategy)`  (from `internal/bind/ObjectTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ObjectTypeAdapter_getFactory_com_google_gson_TypeAdapterFactory_com_google_gson_ToNumber : Func :=
  { name := "com.google.gson.internal.bind.ObjectTypeAdapter.getFactory:com.google.gson.TypeAdapterFactory(com.google.gson.ToNumberStrategy)"
  , params := ["toNumberStrategy"]
  , body := (.ifte
            (.binop "==" (.name "toNumberStrategy") (.field (.name "ToNumberPolicy") "DOUBLE"))
            (.ret
              (.field (.fnref "com.google.gson.internal.bind.ObjectTypeAdapter") "DOUBLE_FACTORY"))
            (.ret
              (.call
                "com.google.gson.internal.bind.ObjectTypeAdapter.newFactory:com.google.gson.TypeAdapterFactory(com.google.gson.ToNumberStrategy)"
                [(.name "toNumberStrategy")]))) }

/-- `com.google.gson.internal.bind.ObjectTypeAdapter.tryBeginNesting:java.lang.Object(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)`  (from `internal/bind/ObjectTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ObjectTypeAdapter_tryBeginNesting_java_lang_Object_com_google_gson_stream_JsonReader_com : Func :=
  { name := "com.google.gson.internal.bind.ObjectTypeAdapter.tryBeginNesting:java.lang.Object(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)"
  , params := ["this", "in", "peeked"]
  , body := (.hole "control:SWITCH") }

/-- `com.google.gson.internal.bind.ObjectTypeAdapter.readTerminal:java.lang.Object(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)`  (from `internal/bind/ObjectTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ObjectTypeAdapter_readTerminal_java_lang_Object_com_google_gson_stream_JsonReader_com_go : Func :=
  { name := "com.google.gson.internal.bind.ObjectTypeAdapter.readTerminal:java.lang.Object(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)"
  , params := ["this", "in", "peeked"]
  , body := (.hole "control:SWITCH") }

/-- `com.google.gson.internal.bind.ObjectTypeAdapter.read:java.lang.Object(com.google.gson.stream.JsonReader)`  (from `internal/bind/ObjectTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ObjectTypeAdapter_read_java_lang_Object_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.bind.ObjectTypeAdapter.read:java.lang.Object(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "peeked" (.call "peek" []))
                (.seq
                  (.assign
                    "current"
                    (.call
                      "com.google.gson.internal.bind.ObjectTypeAdapter.tryBeginNesting:java.lang.Object(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)"
                      [(.name "in"), (.name "peeked")]))
                  (.seq
                    (.ifte
                      (.binop "==" (.name "current") (.lit .unit))
                      (.ret
                        (.call
                          "com.google.gson.internal.bind.ObjectTypeAdapter.readTerminal:java.lang.Object(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)"
                          [(.name "in"), (.name "peeked")]))
                      .skip)
                    (.seq
                      .skip
                      (.seq
                        (.assign "stack" (.hole "op:alloc"))
                        (.seq
                          (.expr (.call "<init>" []))
                          (.loop
                            (.lit (.bool true))
                            (.seq
                              (.loop
                                (.call "hasNext" [])
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "name" (.lit .unit))
                                    (.seq
                                      (.ifte
                                        (.hole "op:instanceOf")
                                        (.assign "name" (.call "nextName" []))
                                        .skip)
                                      (.seq
                                        (.assign "peeked" (.call "peek" []))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "value"
                                        (.call
                                        "com.google.gson.internal.bind.ObjectTypeAdapter.tryBeginNesting:java.lang.Object(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)"
                                        [(.name "in"), (.name "peeked")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "isNesting"
                                        (.binop "!=" (.name "value") (.lit .unit)))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "value") (.lit .unit))
                                        (.assign
                                        "value"
                                        (.call
                                        "com.google.gson.internal.bind.ObjectTypeAdapter.readTerminal:java.lang.Object(com.google.gson.stream.JsonReader,com.google.gson.stream.JsonToken)"
                                        [(.name "in"), (.name "peeked")]))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.hole "op:instanceOf")
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "list" (.hole "op:cast"))
                                        (.expr (.call "add" [(.name "value")]))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "map" (.hole "op:cast"))
                                        (.expr (.call "put" [(.name "name"), (.name "value")])))))
                                        (.ifte
                                        (.name "isNesting")
                                        (.seq
                                        (.expr (.call "addLast" [(.name "current")]))
                                        (.assign "current" (.name "value")))
                                        .skip))))))))))))
                              (.seq
                                (.ifte
                                  (.hole "op:instanceOf")
                                  (.expr (.call "endArray" []))
                                  (.expr (.call "endObject" [])))
                                (.ifte
                                  (.call "isEmpty" [])
                                  (.ret (.name "current"))
                                  (.assign "current" (.call "removeLast" [])))))))))))))) }

/-- `com.google.gson.internal.bind.ObjectTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)`  (from `internal/bind/ObjectTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ObjectTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.bind.ObjectTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "value") (.lit .unit))
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "typeAdapter" (.hole "op:cast"))
                (.seq
                  (.ifte
                    (.hole "op:instanceOf")
                    (.seq
                      (.expr (.call "beginObject" []))
                      (.seq (.expr (.call "endObject" [])) (.ret (.lit .unit))))
                    .skip)
                  (.expr (.call "write" [(.name "out"), (.name "value")])))))) }

/-- `com.google.gson.internal.bind.ObjectTypeAdapter.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_ObjectTypeAdapter__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.ObjectTypeAdapter.<clinit>:void()"
  , params := []
  , body := (.setField
            (.fnref "com.google.gson.internal.bind.ObjectTypeAdapter")
            "DOUBLE_FACTORY"
            (.call
              "com.google.gson.internal.bind.ObjectTypeAdapter.newFactory:com.google.gson.TypeAdapterFactory(com.google.gson.ToNumberStrategy)"
              [(.field (.name "ToNumberPolicy") "DOUBLE")])) }

/-- `com.google.gson.internal.bind.ObjectTypeAdapter.newFactory.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/ObjectTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ObjectTypeAdapter_newFactory_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com : Func :=
  { name := "com.google.gson.internal.bind.ObjectTypeAdapter.newFactory.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "type"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "getRawType" []) (.field (.name "Object") "class"))
              (.ret (.hole "op:cast"))
              .skip)
            (.ret (.lit .unit))) }

/-- `com.google.gson.internal.bind.ObjectTypeAdapter.newFactory.TypeAdapterFactory$0.<init>:void()`  (from `internal/bind/ObjectTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_ObjectTypeAdapter_newFactory_TypeAdapterFactory_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.ObjectTypeAdapter.newFactory.TypeAdapterFactory$0.<init>:void()"
  , params := ["this", "toNumberStrategy"]
  , body := (.setField (.name "this") "toNumberStrategy" (.name "toNumberStrategy")) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.<init>:void(com.google.gson.internal.ConstructorConstructor,com.google.gson.FieldNamingStrategy,com.google.gson.internal.Excluder,com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory,java.util.List)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory__init__void_com_google_gson_internal_ConstructorConstructor : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.<init>:void(com.google.gson.internal.ConstructorConstructor,com.google.gson.FieldNamingStrategy,com.google.gson.internal.Excluder,com.google.gson.internal.bind.JsonAdapterAnnotationTypeAdapterFactory,java.util.List)"
  , params := ["this", "constructorConstructor", "fieldNamingPolicy", "excluder", "jsonAdapterFactory", "reflectionFilters"]
  , body := (.seq
            (.setField (.name "this") "constructorConstructor" (.name "constructorConstructor"))
            (.seq
              (.setField (.name "this") "fieldNamingPolicy" (.name "fieldNamingPolicy"))
              (.seq
                (.setField (.name "this") "excluder" (.name "excluder"))
                (.seq
                  (.setField (.name "this") "jsonAdapterFactory" (.name "jsonAdapterFactory"))
                  (.setField (.name "this") "reflectionFilters" (.name "reflectionFilters")))))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.includeField:boolean(java.lang.reflect.Field,boolean)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_includeField_boolean_java_lang_reflect_Field_boolean_ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.includeField:boolean(java.lang.reflect.Field,boolean)"
  , params := ["this", "f", "serialize"]
  , body := (.ret (.unop "!" (.mcall (.name "this") "excluder" [(.name "f"), (.name "serialize")]))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.getFieldNames:java.util.List(java.lang.reflect.Field)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_getFieldNames_java_util_List_java_lang_reflect_Field_ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.getFieldNames:java.util.List(java.lang.reflect.Field)"
  , params := ["this", "f"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign
                    "annotation"
                    (.call "getAnnotation" [(.field (.name "SerializedName") "class")]))
                  (.seq
                    (.ifte
                      (.binop "==" (.name "annotation") (.lit .unit))
                      (.seq
                        (.assign
                          "fieldName"
                          (.mcall (.name "this") "fieldNamingPolicy" [(.name "f")]))
                        (.assign
                          "alternates"
                          (.mcall (.name "this") "fieldNamingPolicy" [(.name "f")])))
                      (.seq
                        (.assign "fieldName" (.call "value" []))
                        (.assign "alternates" (.call "asList" [(.call "alternate" [])]))))
                    (.seq
                      (.ifte
                        (.call "isEmpty" [])
                        (.ret (.call "singletonList" [(.name "fieldName")]))
                        .skip)
                      (.seq
                        .skip
                        (.seq
                          (.assign "fieldNames" (.hole "op:alloc"))
                          (.seq
                            (.expr
                              (.call "<init>" [(.binop "+" (.call "size" []) (.lit (.int 1)))]))
                            (.seq
                              (.expr (.call "add" [(.name "fieldName")]))
                              (.seq
                                (.expr (.call "addAll" [(.name "alternates")]))
                                (.ret (.name "fieldNames"))))))))))))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_create_com_google_gson_TypeAdapter_com_google_gson_Gson_com : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "type"]
  , body := (.seq
            .skip
            (.seq
              (.assign "raw" (.call "getRawType" []))
              (.seq
                (.ifte
                  (.unop "!" (.mcall (.name "Object") "class" [(.name "raw")]))
                  (.ret (.lit .unit))
                  .skip)
                (.seq
                  (.ifte
                    (.call
                      "com.google.gson.internal.reflect.ReflectionHelper.isAnonymousOrNonStaticLocal:boolean(java.lang.Class)"
                      [(.name "raw")])
                    (.seq
                      .skip
                      (.seq
                        (.assign "$obj0" (.hole "op:alloc"))
                        (.seq
                          (.expr
                            (.call
                              "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.create.TypeAdapter$0.<init>:void()"
                              [(.name "this")]))
                          (.ret (.name "$obj0")))))
                    .skip)
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "filterResult"
                        (.call
                          "com.google.gson.internal.ReflectionAccessFilterHelper.getFilterResult:com.google.gson.ReflectionAccessFilter.FilterResult(java.util.List,java.lang.Class)"
                          [(.field (.name "this") "reflectionFilters"), (.name "raw")]))
                      (.seq
                        (.ifte
                          (.binop
                            "=="
                            (.name "filterResult")
                            (.field (.name "FilterResult") "BLOCK_ALL"))
                          (.hole "control:THROW")
                          .skip)
                        (.seq
                          .skip
                          (.seq
                            (.assign
                              "blockInaccessible"
                              (.binop
                                "=="
                                (.name "filterResult")
                                (.field (.name "FilterResult") "BLOCK_INACCESSIBLE")))
                            (.seq
                              (.ifte
                                (.call
                                  "com.google.gson.internal.reflect.ReflectionHelper.isRecord:boolean(java.lang.Class)"
                                  [(.name "raw")])
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "adapter" (.hole "op:cast"))
                                    (.ret (.name "adapter"))))
                                .skip)
                              (.seq
                                .skip
                                (.seq
                                  (.assign
                                    "constructor"
                                    (.mcall
                                      (.name "this")
                                      "constructorConstructor"
                                      [(.name "type"), (.lit (.bool true))]))
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign "$obj3" (.hole "op:alloc"))
                                      (.seq
                                        (.expr
                                        (.call
                                        "<init>"
                                        [ (.name "constructor")
                                        , (.call
                                        "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.getBoundFields:com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData(com.google.gson.Gson,com.google.gson.reflect.TypeToken,java.lang.Class,boolean,boolean)"
                                        [ (.name "gson")
                                        , (.name "type")
                                        , (.name "raw")
                                        , (.name "blockInaccessible")
                                        , (.lit (.bool false)) ]) ]))
                                        (.ret (.name "$obj3"))))))))))))))))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.checkAccessible:void(java.lang.Object,java.lang.reflect.AccessibleObject)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_checkAccessible_void_java_lang_Object_java_lang_reflect_Acc : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.checkAccessible:void(java.lang.Object,java.lang.reflect.AccessibleObject)"
  , params := ["object", "member"]
  , body := (.ifte
            (.unop
              "!"
              (.call
                "com.google.gson.internal.ReflectionAccessFilterHelper.canAccess:boolean(java.lang.reflect.AccessibleObject,java.lang.Object)"
                [ (.name "member")
                , (.cond
                    (.call "isStatic" [(.call "getModifiers" [])])
                    (.lit .unit)
                    (.name "object")) ]))
            (.seq
              .skip
              (.seq
                (.assign
                  "memberDescription"
                  (.call
                    "com.google.gson.internal.reflect.ReflectionHelper.getAccessibleObjectDescription:java.lang.String(java.lang.reflect.AccessibleObject,boolean)"
                    [(.name "member"), (.lit (.bool true))]))
                (.hole "control:THROW")))
            .skip) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.createBoundField:com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField(com.google.gson.Gson,java.lang.reflect.Field,java.lang.reflect.Method,java.lang.String,com.google.gson.reflect.TypeToken,boolean,boolean)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_createBoundField_com_google_gson_internal_bind_ReflectiveTy : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.createBoundField:com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField(com.google.gson.Gson,java.lang.reflect.Field,java.lang.reflect.Method,java.lang.String,com.google.gson.reflect.TypeToken,boolean,boolean)"
  , params := ["this", "context", "field", "accessor", "serializedName", "fieldType", "serialize", "blockInaccessible"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "isPrimitive"
                (.call
                  "com.google.gson.internal.Primitives.isPrimitive:boolean(java.lang.reflect.Type)"
                  [(.call "getRawType" [])]))
              (.seq
                .skip
                (.seq
                  (.assign "modifiers" (.call "getModifiers" []))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "isStaticFinalField"
                        (.binop
                          "&&"
                          (.call "isStatic" [(.name "modifiers")])
                          (.call "isFinal" [(.name "modifiers")])))
                      (.seq
                        .skip
                        (.seq
                          (.assign
                            "annotation"
                            (.call "getAnnotation" [(.field (.name "JsonAdapter") "class")]))
                          (.seq
                            .skip
                            (.seq
                              (.assign "mapped" (.lit .unit))
                              (.seq
                                (.ifte
                                  (.binop "!=" (.name "annotation") (.lit .unit))
                                  (.assign
                                    "mapped"
                                    (.mcall
                                      (.name "this")
                                      "jsonAdapterFactory"
                                      [ (.field (.name "this") "constructorConstructor")
                                      , (.name "context")
                                      , (.name "fieldType")
                                      , (.name "annotation")
                                      , (.lit (.bool false)) ]))
                                  .skip)
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign
                                      "jsonAdapterPresent"
                                      (.binop "!=" (.name "mapped") (.lit .unit)))
                                    (.seq
                                      (.ifte
                                        (.binop "==" (.name "mapped") (.lit .unit))
                                        (.assign
                                        "mapped"
                                        (.call "getAdapter" [(.name "fieldType")]))
                                        .skip)
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign "typeAdapter" (.hole "op:cast"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.name "serialize")
                                        (.assign
                                        "writeTypeAdapter"
                                        (.cond
                                        (.name "jsonAdapterPresent")
                                        (.name "typeAdapter")
                                        (.hole "expr:BLOCK-impure")))
                                        (.assign "writeTypeAdapter" (.name "typeAdapter")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "$obj6" (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "<init>"
                                        [ (.name "serializedName")
                                        , (.name "field")
                                        , (.name "this")
                                        , (.name "isPrimitive")
                                        , (.name "isStaticFinalField")
                                        , (.name "typeAdapter")
                                        , (.name "writeTypeAdapter")
                                        , (.name "accessor")
                                        , (.name "blockInaccessible")
                                        , (.name "field")
                                        , (.name "serializedName") ]))
                                        (.ret (.name "$obj6"))))))))))))))))))))))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData.<init>:void(java.util.Map,java.util.List)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_FieldsData__init__void_java_util_Map_java_util_List_ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData.<init>:void(java.util.Map,java.util.List)"
  , params := ["this", "deserializedFields", "serializedFields"]
  , body := (.seq
            (.setField (.name "this") "deserializedFields" (.name "deserializedFields"))
            (.setField (.name "this") "serializedFields" (.name "serializedFields"))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_FieldsData__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData")
              "EMPTY"
              (.hole "op:alloc"))
            (.expr
              (.mcall
                (.fnref "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData")
                "EMPTY"
                [(.call "emptyMap" []), (.call "emptyList" [])]))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.createDuplicateFieldException:java.lang.IllegalArgumentException(java.lang.Class,java.lang.String,java.lang.reflect.Field,java.lang.reflect.Field)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_createDuplicateFieldException_java_lang_IllegalArgumentExce : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.createDuplicateFieldException:java.lang.IllegalArgumentException(java.lang.Class,java.lang.String,java.lang.reflect.Field,java.lang.reflect.Field)"
  , params := ["declaringType", "duplicateName", "field1", "field2"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.getBoundFields:com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData(com.google.gson.Gson,com.google.gson.reflect.TypeToken,java.lang.Class,boolean,boolean)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_getBoundFields_com_google_gson_internal_bind_ReflectiveType : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.getBoundFields:com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData(com.google.gson.Gson,com.google.gson.reflect.TypeToken,java.lang.Class,boolean,boolean)"
  , params := ["this", "context", "type", "raw", "blockInaccessible", "isRecord"]
  , body := (.seq
            (.ifte (.call "isInterface" []) (.ret (.field (.name "FieldsData") "EMPTY")) .skip)
            (.seq
              .skip
              (.seq
                (.assign "deserializedFields" (.hole "op:alloc"))
                (.seq
                  (.expr (.call "<init>" []))
                  (.seq
                    .skip
                    (.seq
                      (.assign "serializedFields" (.hole "op:alloc"))
                      (.seq
                        (.expr (.call "<init>" []))
                        (.seq
                          .skip
                          (.seq
                            (.assign "originalRaw" (.name "raw"))
                            (.seq
                              (.loop
                                (.binop "!=" (.name "raw") (.field (.name "Object") "class"))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "fields" (.call "getDeclaredFields" []))
                                    (.seq
                                      (.ifte
                                        (.binop
                                        "&&"
                                        (.binop "!=" (.name "raw") (.name "originalRaw"))
                                        (.binop ">" (.hole "op:sizeOf") (.lit (.int 0))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "filterResult"
                                        (.call
                                        "com.google.gson.internal.ReflectionAccessFilterHelper.getFilterResult:com.google.gson.ReflectionAccessFilter.FilterResult(java.util.List,java.lang.Class)"
                                        [(.field (.name "this") "reflectionFilters"), (.name "raw")]))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.name "filterResult")
                                        (.field (.name "FilterResult") "BLOCK_ALL"))
                                        (.hole "control:THROW")
                                        .skip)
                                        (.assign
                                        "blockInaccessible"
                                        (.binop
                                        "=="
                                        (.name "filterResult")
                                        (.field (.name "FilterResult") "BLOCK_INACCESSIBLE"))))))
                                        .skip)
                                      (.seq
                                        (.hole "control:FOR")
                                        (.seq
                                        (.assign
                                        "type"
                                        (.call
                                        "get"
                                        [ (.call
                                        "com.google.gson.internal.GsonTypes.resolve:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Class,java.lang.reflect.Type)"
                                        [ (.call "getType" [])
                                        , (.name "raw")
                                        , (.call "getGenericSuperclass" []) ]) ]))
                                        (.assign "raw" (.call "getRawType" []))))))))
                              (.seq
                                .skip
                                (.seq
                                  (.assign "$obj13" (.hole "op:alloc"))
                                  (.seq
                                    (.expr
                                      (.call
                                        "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData.<init>:void(java.util.Map,java.util.List)"
                                        [ (.name "deserializedFields")
                                        , (.hole "expr:BLOCK-impure")
                                        , (.name "this") ]))
                                    (.ret (.name "$obj13"))))))))))))))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField.<init>:void(java.lang.String,java.lang.reflect.Field)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_BoundField__init__void_java_lang_String_java_lang_reflect_F : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField.<init>:void(java.lang.String,java.lang.reflect.Field)"
  , params := ["this", "serializedName", "field"]
  , body := (.seq
            (.setField (.name "this") "serializedName" (.name "serializedName"))
            (.seq
              (.setField (.name "this") "field" (.name "field"))
              (.setField (.name "this") "fieldName" (.call "getName" [])))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_BoundField_write_void_com_google_gson_stream_JsonWriter_jav : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)"
  , params := ["this", "writer", "source"]
  , body := .skip }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField.readIntoArray:void(com.google.gson.stream.JsonReader,int,java.lang.Object[])`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_BoundField_readIntoArray_void_com_google_gson_stream_JsonRe : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField.readIntoArray:void(com.google.gson.stream.JsonReader,int,java.lang.Object[])"
  , params := ["this", "reader", "index", "target"]
  , body := .skip }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField.readIntoField:void(com.google.gson.stream.JsonReader,java.lang.Object)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_BoundField_readIntoField_void_com_google_gson_stream_JsonRe : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField.readIntoField:void(com.google.gson.stream.JsonReader,java.lang.Object)"
  , params := ["this", "reader", "target"]
  , body := .skip }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.<init>:void(com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_Adapter__init__void_com_google_gson_internal_bind_Reflectiv : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.<init>:void(com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData)"
  , params := ["this", "fieldsData"]
  , body := (.setField (.name "this") "fieldsData" (.name "fieldsData")) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_Adapter_write_void_com_google_gson_stream_JsonWriter_java_l : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "value") (.lit .unit))
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              (.expr (.call "beginObject" []))
              (.seq
                (.tryCatch
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "$iterLocal1"
                        (.mcall (.field (.name "this") "fieldsData") "serializedFields" []))
                      (.loop
                        (.call "hasNext" [])
                        (.seq
                          .skip
                          (.seq
                            (.assign "boundField" (.call "next" []))
                            (.expr
                              (.call
                                "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)"
                                [(.name "out"), (.name "value")])))))))
                  "__exc"
                  (.hole "control:THROW"))
                (.expr (.call "endObject" []))))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.read:java.lang.Object(com.google.gson.stream.JsonReader)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_Adapter_read_java_lang_Object_com_google_gson_stream_JsonRe : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.read:java.lang.Object(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign
                  "accumulator"
                  (.call
                    "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.createAccumulator:java.lang.Object()"
                    []))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "deserializedFields"
                      (.field (.field (.name "this") "fieldsData") "deserializedFields"))
                    (.seq
                      (.hole "control:TRY-multiCatch")
                      (.seq
                        (.expr (.call "endObject" []))
                        (.ret
                          (.call
                            "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.finalize:java.lang.Object(java.lang.Object)"
                            [(.name "accumulator")]))))))))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.createAccumulator:java.lang.Object()`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_Adapter_createAccumulator_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.createAccumulator:java.lang.Object()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.readField:void(java.lang.Object,com.google.gson.stream.JsonReader,com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_Adapter_readField_void_java_lang_Object_com_google_gson_str : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.readField:void(java.lang.Object,com.google.gson.stream.JsonReader,com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField)"
  , params := ["this", "accumulator", "in", "field"]
  , body := .skip }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.finalize:java.lang.Object(java.lang.Object)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_Adapter_finalize_java_lang_Object_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.finalize:java.lang.Object(java.lang.Object)"
  , params := ["this", "accumulator"]
  , body := .skip }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldReflectionAdapter.<init>:void(com.google.gson.internal.ObjectConstructor,com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_FieldReflectionAdapter__init__void_com_google_gson_internal : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldReflectionAdapter.<init>:void(com.google.gson.internal.ObjectConstructor,com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData)"
  , params := ["this", "constructor", "fieldsData"]
  , body := (.seq
            (.expr
              (.call
                "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.<init>:void(com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData)"
                [(.name "fieldsData")]))
            (.setField (.name "this") "constructor" (.name "constructor"))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldReflectionAdapter.createAccumulator:java.lang.Object()`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_FieldReflectionAdapter_createAccumulator_java_lang_Object__ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldReflectionAdapter.createAccumulator:java.lang.Object()"
  , params := ["this"]
  , body := (.ret (.mcall (.name "this") "constructor" [])) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldReflectionAdapter.readField:void(java.lang.Object,com.google.gson.stream.JsonReader,com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_FieldReflectionAdapter_readField_void_java_lang_Object_com_ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldReflectionAdapter.readField:void(java.lang.Object,com.google.gson.stream.JsonReader,com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField)"
  , params := ["this", "accumulator", "in", "field"]
  , body := (.expr
            (.call
              "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField.readIntoField:void(com.google.gson.stream.JsonReader,java.lang.Object)"
              [(.name "in"), (.name "accumulator")])) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldReflectionAdapter.finalize:java.lang.Object(java.lang.Object)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_FieldReflectionAdapter_finalize_java_lang_Object_java_lang_ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldReflectionAdapter.finalize:java.lang.Object(java.lang.Object)"
  , params := ["this", "accumulator"]
  , body := (.ret (.name "accumulator")) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter.<init>:void(java.lang.Class,com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData,boolean)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_RecordAdapter__init__void_java_lang_Class_com_google_gson_i : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter.<init>:void(java.lang.Class,com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData,boolean)"
  , params := ["this", "raw", "fieldsData", "blockInaccessible"]
  , body := (.seq
            (.setField (.name "this") "componentIndices" (.hole "op:alloc"))
            (.seq
              (.expr (.mcall (.name "this") "componentIndices" []))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$Adapter.<init>:void(com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$FieldsData)"
                    [(.name "fieldsData")]))
                (.seq
                  (.setField
                    (.name "this")
                    "constructor"
                    (.call
                      "com.google.gson.internal.reflect.ReflectionHelper.getCanonicalRecordConstructor:java.lang.reflect.Constructor(java.lang.Class)"
                      [(.name "raw")]))
                  (.seq
                    (.ifte
                      (.name "blockInaccessible")
                      (.expr
                        (.mcall
                          (.name "this")
                          "outerClass"
                          [(.lit .unit), (.field (.name "this") "constructor")]))
                      (.expr (.call "makeAccessible" [(.field (.name "this") "constructor")])))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "componentNames"
                          (.call
                            "com.google.gson.internal.reflect.ReflectionHelper.getRecordComponentNames:java.lang.String[](java.lang.Class)"
                            [(.name "raw")]))
                        (.seq
                          (.hole "control:FOR")
                          (.seq
                            .skip
                            (.seq
                              (.assign "parameterTypes" (.mcall (.name "this") "constructor" []))
                              (.seq
                                (.setField
                                  (.name "this")
                                  "constructorArgsDefaults"
                                  (.hole "op:alloc"))
                                (.hole "control:FOR")))))))))))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter.primitiveDefaults:java.util.Map()`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_RecordAdapter_primitiveDefaults_java_util_Map__ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter.primitiveDefaults:java.util.Map()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "zeroes" (.hole "op:alloc"))
              (.seq
                (.expr (.call "<init>" []))
                (.seq
                  (.expr (.call "put" [(.field (.name "byte") "class"), (.hole "op:cast")]))
                  (.seq
                    (.expr (.call "put" [(.field (.name "short") "class"), (.hole "op:cast")]))
                    (.seq
                      (.expr (.call "put" [(.field (.name "int") "class"), (.lit (.int 0))]))
                      (.seq
                        (.expr
                          (.call "put" [(.field (.name "long") "class"), (.hole "lit:unquoted")]))
                        (.seq
                          (.expr
                            (.call "put" [(.field (.name "float") "class"), (.hole "lit:unquoted")]))
                          (.seq
                            (.expr
                              (.call
                                "put"
                                [(.field (.name "double") "class"), (.hole "lit:unquoted")]))
                            (.seq
                              (.expr
                                (.call "put" [(.field (.name "char") "class"), (.lit (.str "\\0"))]))
                              (.seq
                                (.expr
                                  (.call
                                    "put"
                                    [(.field (.name "boolean") "class"), (.lit (.bool false))]))
                                (.ret (.name "zeroes"))))))))))))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter.createAccumulator:java.lang.Object[]()`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_RecordAdapter_createAccumulator_java_lang_Object____ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter.createAccumulator:java.lang.Object[]()"
  , params := ["this"]
  , body := (.ret (.mcall (.name "this") "constructorArgsDefaults" [])) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter.readField:void(java.lang.Object[],com.google.gson.stream.JsonReader,com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_RecordAdapter_readField_void_java_lang_Object___com_google_ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter.readField:void(java.lang.Object[],com.google.gson.stream.JsonReader,com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$BoundField)"
  , params := ["this", "accumulator", "in", "field"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "componentIndex"
                (.mcall (.name "this") "componentIndices" [(.field (.name "field") "fieldName")]))
              (.seq
                (.ifte
                  (.binop "==" (.name "componentIndex") (.lit .unit))
                  (.hole "control:THROW")
                  .skip)
                (.expr
                  (.call
                    "readIntoArray"
                    [(.name "in"), (.name "componentIndex"), (.name "accumulator")]))))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter.finalize:java.lang.Object(java.lang.Object[])`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_RecordAdapter_finalize_java_lang_Object_java_lang_Object___ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter.finalize:java.lang.Object(java.lang.Object[])"
  , params := ["this", "accumulator"]
  , body := (.hole "control:TRY-multiCatch") }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_RecordAdapter__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter.<clinit>:void()"
  , params := []
  , body := (.setField
            (.fnref "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter")
            "PRIMITIVE_DEFAULTS"
            (.call
              "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory$RecordAdapter.primitiveDefaults:java.util.Map()"
              [])) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.create.TypeAdapter$0.read:java.lang.Object(com.google.gson.stream.JsonReader)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_create_TypeAdapter_0_read_java_lang_Object_com_google_gson_ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.create.TypeAdapter$0.read:java.lang.Object(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq (.expr (.call "skipValue" [])) (.ret (.lit .unit))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.create.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_create_TypeAdapter_0_write_void_com_google_gson_stream_Json : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.create.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)"
  , params := ["this", "out", "value"]
  , body := (.expr (.call "nullValue" [])) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.create.TypeAdapter$0.toString:<unresolvedSignature>(0)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_create_TypeAdapter_0_toString__unresolvedSignature__0_ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.create.TypeAdapter$0.toString:<unresolvedSignature>(0)"
  , params := ["this"]
  , body := (.ret (.lit (.str "AnonymousOrNonStaticLocalClassAdapter"))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.create.TypeAdapter$0.<init>:void()`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_create_TypeAdapter_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.create.TypeAdapter$0.<init>:void()"
  , params := ["this", "outerClass"]
  , body := (.setField (.name "this") "outerClass" (.name "outerClass")) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.createBoundField.BoundField$0.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_createBoundField_BoundField_0_write_void_com_google_gson_st : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.createBoundField.BoundField$0.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)"
  , params := ["this", "writer", "source"]
  , body := (.seq
            (.ifte
              (.field (.name "this") "blockInaccessible")
              (.ifte
                (.binop "==" (.field (.name "this") "accessor") (.lit .unit))
                (.expr
                  (.call
                    "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.checkAccessible:void(java.lang.Object,java.lang.reflect.AccessibleObject)"
                    [(.name "source"), (.field (.name "this") "field")]))
                (.expr
                  (.call
                    "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.checkAccessible:void(java.lang.Object,java.lang.reflect.AccessibleObject)"
                    [(.name "source"), (.field (.name "this") "accessor")])))
              .skip)
            (.seq
              .skip
              (.seq
                (.ifte
                  (.binop "!=" (.field (.name "this") "accessor") (.lit .unit))
                  (.tryCatch
                    (.assign
                      "fieldValue"
                      (.mcall
                        (.name "this")
                        "accessor"
                        [(.name "source"), (.hole "op:arrayInitializer")]))
                    "__exc"
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "accessorDescription"
                          (.call
                            "com.google.gson.internal.reflect.ReflectionHelper.getAccessibleObjectDescription:java.lang.String(java.lang.reflect.AccessibleObject,boolean)"
                            [(.field (.name "this") "accessor"), (.lit (.bool false))]))
                        (.hole "control:THROW"))))
                  (.assign "fieldValue" (.mcall (.name "this") "field" [(.name "source")])))
                (.seq
                  .skip
                  (.seq
                    (.assign "isSameObject" (.binop "==" (.name "fieldValue") (.name "source")))
                    (.seq
                      (.ifte (.name "isSameObject") (.ret (.lit .unit)) .skip)
                      (.seq
                        (.expr (.call "name" [(.field (.name "this") "serializedName")]))
                        (.expr
                          (.mcall
                            (.name "this")
                            "writeTypeAdapter"
                            [(.name "writer"), (.name "fieldValue")]))))))))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.createBoundField.BoundField$0.readIntoArray:void(com.google.gson.stream.JsonReader,int,java.lang.Object[])`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_createBoundField_BoundField_0_readIntoArray_void_com_google : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.createBoundField.BoundField$0.readIntoArray:void(com.google.gson.stream.JsonReader,int,java.lang.Object[])"
  , params := ["this", "reader", "index", "target"]
  , body := (.seq
            .skip
            (.seq
              (.assign "fieldValue" (.mcall (.name "this") "typeAdapter" [(.name "reader")]))
              (.seq
                (.ifte
                  (.binop
                    "&&"
                    (.binop "==" (.name "fieldValue") (.lit .unit))
                    (.field (.name "this") "isPrimitive"))
                  (.hole "control:THROW")
                  .skip)
                (.setIndex (.name "target") (.name "index") (.name "fieldValue"))))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.createBoundField.BoundField$0.readIntoField:void(com.google.gson.stream.JsonReader,java.lang.Object)`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_createBoundField_BoundField_0_readIntoField_void_com_google : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.createBoundField.BoundField$0.readIntoField:void(com.google.gson.stream.JsonReader,java.lang.Object)"
  , params := ["this", "reader", "target"]
  , body := (.seq
            .skip
            (.seq
              (.assign "fieldValue" (.mcall (.name "this") "typeAdapter" [(.name "reader")]))
              (.ifte
                (.binop
                  "||"
                  (.binop "!=" (.name "fieldValue") (.lit .unit))
                  (.unop "!" (.field (.name "this") "isPrimitive")))
                (.seq
                  (.ifte
                    (.field (.name "this") "blockInaccessible")
                    (.expr
                      (.call
                        "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.checkAccessible:void(java.lang.Object,java.lang.reflect.AccessibleObject)"
                        [(.name "target"), (.field (.name "this") "field")]))
                    (.ifte
                      (.field (.name "this") "isStaticFinalField")
                      (.seq
                        .skip
                        (.seq
                          (.assign
                            "fieldDescription"
                            (.call
                              "com.google.gson.internal.reflect.ReflectionHelper.getAccessibleObjectDescription:java.lang.String(java.lang.reflect.AccessibleObject,boolean)"
                              [(.field (.name "this") "field"), (.lit (.bool false))]))
                          (.hole "control:THROW")))
                      .skip))
                  (.expr (.mcall (.name "this") "field" [(.name "target"), (.name "fieldValue")])))
                .skip))) }

/-- `com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.createBoundField.BoundField$0.<init>:void()`  (from `internal/bind/ReflectiveTypeAdapterFactory.java`) -/
def f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_createBoundField_BoundField_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.ReflectiveTypeAdapterFactory.createBoundField.BoundField$0.<init>:void()"
  , params := ["this", "outerClass", "isPrimitive", "isStaticFinalField", "typeAdapter", "writeTypeAdapter", "accessor", "blockInaccessible", "field", "serializedName"]
  , body := (.seq
            (.setField (.name "this") "outerClass" (.name "outerClass"))
            (.seq
              (.setField (.name "this") "isPrimitive" (.name "isPrimitive"))
              (.seq
                (.setField (.name "this") "isStaticFinalField" (.name "isStaticFinalField"))
                (.seq
                  (.setField (.name "this") "typeAdapter" (.name "typeAdapter"))
                  (.seq
                    (.setField (.name "this") "writeTypeAdapter" (.name "writeTypeAdapter"))
                    (.seq
                      (.setField (.name "this") "accessor" (.name "accessor"))
                      (.seq
                        (.setField (.name "this") "blockInaccessible" (.name "blockInaccessible"))
                        (.seq
                          (.setField (.name "this") "field" (.name "field"))
                          (.setField (.name "this") "serializedName" (.name "serializedName")))))))))) }

/-- `com.google.gson.internal.bind.SerializationDelegatingTypeAdapter.getSerializationDelegate:com.google.gson.TypeAdapter()`  (from `internal/bind/SerializationDelegatingTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_SerializationDelegatingTypeAdapter_getSerializationDelegate_com_google_gson_TypeAdapter_ : Func :=
  { name := "com.google.gson.internal.bind.SerializationDelegatingTypeAdapter.getSerializationDelegate:com.google.gson.TypeAdapter()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.SerializationDelegatingTypeAdapter.<init>:void()`  (from `internal/bind/SerializationDelegatingTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_SerializationDelegatingTypeAdapter__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.SerializationDelegatingTypeAdapter.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TreeTypeAdapter.<init>:void(com.google.gson.JsonSerializer,com.google.gson.JsonDeserializer,com.google.gson.Gson,com.google.gson.reflect.TypeToken,com.google.gson.TypeAdapterFactory,boolean)`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter__init__void_com_google_gson_JsonSerializer_com_google_gson_JsonDeseriali : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter.<init>:void(com.google.gson.JsonSerializer,com.google.gson.JsonDeserializer,com.google.gson.Gson,com.google.gson.reflect.TypeToken,com.google.gson.TypeAdapterFactory,boolean)"
  , params := ["this", "serializer", "deserializer", "gson", "typeToken", "skipPast", "nullSafe"]
  , body := (.seq
            (.setField (.name "this") "context" (.hole "op:alloc"))
            (.seq
              (.expr (.mcall (.name "this") "context" [(.name "this")]))
              (.seq
                (.setField (.name "this") "serializer" (.name "serializer"))
                (.seq
                  (.setField (.name "this") "deserializer" (.name "deserializer"))
                  (.seq
                    (.setField (.name "this") "gson" (.name "gson"))
                    (.seq
                      (.setField (.name "this") "typeToken" (.name "typeToken"))
                      (.seq
                        (.setField
                          (.name "this")
                          "skipPastForGetDelegateAdapter"
                          (.name "skipPast"))
                        (.setField (.name "this") "nullSafe" (.name "nullSafe"))))))))) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter.<init>:void(com.google.gson.JsonSerializer,com.google.gson.JsonDeserializer,com.google.gson.Gson,com.google.gson.reflect.TypeToken,com.google.gson.TypeAdapterFactory)`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter__init__void_com_google_gson_JsonSerializer_com_google_gson_JsonDeseriali' : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter.<init>:void(com.google.gson.JsonSerializer,com.google.gson.JsonDeserializer,com.google.gson.Gson,com.google.gson.reflect.TypeToken,com.google.gson.TypeAdapterFactory)"
  , params := ["this", "serializer", "deserializer", "gson", "typeToken", "skipPast"]
  , body := (.expr
            (.call
              "<init>"
              [ (.name "serializer")
              , (.name "deserializer")
              , (.name "gson")
              , (.name "typeToken")
              , (.name "skipPast")
              , (.lit (.bool true)) ])) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter.read:java.lang.Object(com.google.gson.stream.JsonReader)`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter_read_java_lang_Object_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter.read:java.lang.Object(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.field (.name "this") "deserializer") (.lit .unit))
              (.ret (.call "read" [(.name "in")]))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign
                  "value"
                  (.call
                    "com.google.gson.internal.Streams.parse:com.google.gson.JsonElement(com.google.gson.stream.JsonReader)"
                    [(.name "in")]))
                (.seq
                  (.ifte
                    (.binop "&&" (.field (.name "this") "nullSafe") (.call "isJsonNull" []))
                    (.ret (.lit .unit))
                    .skip)
                  (.ret
                    (.mcall
                      (.name "this")
                      "deserializer"
                      [ (.name "value")
                      , (.mcall (.name "this") "typeToken" [])
                      , (.field (.name "this") "context") ])))))) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.field (.name "this") "serializer") (.lit .unit))
              (.seq (.expr (.call "write" [(.name "out"), (.name "value")])) (.ret (.lit .unit)))
              .skip)
            (.seq
              (.ifte
                (.binop
                  "&&"
                  (.field (.name "this") "nullSafe")
                  (.binop "==" (.name "value") (.lit .unit)))
                (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
                .skip)
              (.seq
                .skip
                (.seq
                  (.assign
                    "tree"
                    (.mcall
                      (.name "this")
                      "serializer"
                      [ (.name "value")
                      , (.mcall (.name "this") "typeToken" [])
                      , (.field (.name "this") "context") ]))
                  (.expr
                    (.call
                      "com.google.gson.internal.Streams.write:void(com.google.gson.JsonElement,com.google.gson.stream.JsonWriter)"
                      [(.name "tree"), (.name "out")])))))) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter.delegate:com.google.gson.TypeAdapter()`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter_delegate_com_google_gson_TypeAdapter__ : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter.delegate:com.google.gson.TypeAdapter()"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "d" (.field (.name "this") "delegate"))
              (.seq
                (.ifte
                  (.binop "==" (.name "d") (.lit .unit))
                  (.assign "d" (.hole "op:assignment"))
                  .skip)
                (.ret (.name "d"))))) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter.getSerializationDelegate:com.google.gson.TypeAdapter()`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter_getSerializationDelegate_com_google_gson_TypeAdapter__ : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter.getSerializationDelegate:com.google.gson.TypeAdapter()"
  , params := ["this"]
  , body := (.ret
            (.cond
              (.binop "!=" (.field (.name "this") "serializer") (.lit .unit))
              (.name "this")
              (.call
                "com.google.gson.internal.bind.TreeTypeAdapter.delegate:com.google.gson.TypeAdapter()"
                []))) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter.newFactory:com.google.gson.TypeAdapterFactory(com.google.gson.reflect.TypeToken,java.lang.Object)`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter_newFactory_com_google_gson_TypeAdapterFactory_com_google_gson_reflect_Ty : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter.newFactory:com.google.gson.TypeAdapterFactory(com.google.gson.reflect.TypeToken,java.lang.Object)"
  , params := ["exactType", "typeAdapter"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj0" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.bind.TreeTypeAdapter$SingleTypeFactory.<init>:void(java.lang.Object,com.google.gson.reflect.TypeToken,boolean,java.lang.Class)"
                    [(.name "typeAdapter"), (.name "exactType"), (.lit (.bool false)), (.lit .unit)]))
                (.ret (.name "$obj0"))))) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter.newFactoryWithMatchRawType:com.google.gson.TypeAdapterFactory(com.google.gson.reflect.TypeToken,java.lang.Object)`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter_newFactoryWithMatchRawType_com_google_gson_TypeAdapterFactory_com_google : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter.newFactoryWithMatchRawType:com.google.gson.TypeAdapterFactory(com.google.gson.reflect.TypeToken,java.lang.Object)"
  , params := ["exactType", "typeAdapter"]
  , body := (.seq
            .skip
            (.seq
              (.assign "matchRawType" (.binop "==" (.call "getType" []) (.call "getRawType" [])))
              (.seq
                .skip
                (.seq
                  (.assign "$obj1" (.hole "op:alloc"))
                  (.seq
                    (.expr
                      (.call
                        "com.google.gson.internal.bind.TreeTypeAdapter$SingleTypeFactory.<init>:void(java.lang.Object,com.google.gson.reflect.TypeToken,boolean,java.lang.Class)"
                        [ (.name "typeAdapter")
                        , (.name "exactType")
                        , (.name "matchRawType")
                        , (.lit .unit) ]))
                    (.ret (.name "$obj1"))))))) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter.newTypeHierarchyFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,java.lang.Object)`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter_newTypeHierarchyFactory_com_google_gson_TypeAdapterFactory_java_lang_Cla : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter.newTypeHierarchyFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,java.lang.Object)"
  , params := ["hierarchyType", "typeAdapter"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj2" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.bind.TreeTypeAdapter$SingleTypeFactory.<init>:void(java.lang.Object,com.google.gson.reflect.TypeToken,boolean,java.lang.Class)"
                    [ (.name "typeAdapter")
                    , (.lit .unit)
                    , (.lit (.bool false))
                    , (.name "hierarchyType") ]))
                (.ret (.name "$obj2"))))) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter$SingleTypeFactory.<init>:void(java.lang.Object,com.google.gson.reflect.TypeToken,boolean,java.lang.Class)`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter_SingleTypeFactory__init__void_java_lang_Object_com_google_gson_reflect_T : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter$SingleTypeFactory.<init>:void(java.lang.Object,com.google.gson.reflect.TypeToken,boolean,java.lang.Class)"
  , params := ["this", "typeAdapter", "exactType", "matchRawType", "hierarchyType"]
  , body := (.seq
            (.setField
              (.name "this")
              "serializer"
              (.cond (.hole "op:instanceOf") (.hole "op:cast") (.lit .unit)))
            (.seq
              (.setField
                (.name "this")
                "deserializer"
                (.cond (.hole "op:instanceOf") (.hole "op:cast") (.lit .unit)))
              (.seq
                (.ifte
                  (.binop
                    "&&"
                    (.binop "==" (.field (.name "this") "serializer") (.lit .unit))
                    (.binop "==" (.field (.name "this") "deserializer") (.lit .unit)))
                  (.seq
                    (.expr (.call "requireNonNull" [(.name "typeAdapter")]))
                    (.hole "control:THROW"))
                  .skip)
                (.seq
                  (.setField (.name "this") "exactType" (.name "exactType"))
                  (.seq
                    (.setField (.name "this") "matchRawType" (.name "matchRawType"))
                    (.setField (.name "this") "hierarchyType" (.name "hierarchyType"))))))) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter$SingleTypeFactory.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter_SingleTypeFactory_create_com_google_gson_TypeAdapter_com_google_gson_Gso : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter$SingleTypeFactory.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "type"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "matches"
                (.cond
                  (.binop "!=" (.field (.name "this") "exactType") (.lit .unit))
                  (.binop
                    "||"
                    (.mcall (.name "this") "exactType" [(.name "type")])
                    (.binop
                      "&&"
                      (.field (.name "this") "matchRawType")
                      (.binop "==" (.mcall (.name "this") "exactType" []) (.call "getRawType" []))))
                  (.mcall (.name "this") "hierarchyType" [(.call "getRawType" [])])))
              (.ret (.cond (.name "matches") (.hole "expr:BLOCK-impure") (.lit .unit))))) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter$GsonContextImpl.serialize:com.google.gson.JsonElement(java.lang.Object)`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter_GsonContextImpl_serialize_com_google_gson_JsonElement_java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter$GsonContextImpl.serialize:com.google.gson.JsonElement(java.lang.Object)"
  , params := ["this", "src"]
  , body := (.ret (.mcall (.field (.name "this") "outerClass") "gson" [(.name "src")])) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter$GsonContextImpl.serialize:com.google.gson.JsonElement(java.lang.Object,java.lang.reflect.Type)`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter_GsonContextImpl_serialize_com_google_gson_JsonElement_java_lang_Object_j : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter$GsonContextImpl.serialize:com.google.gson.JsonElement(java.lang.Object,java.lang.reflect.Type)"
  , params := ["this", "src", "typeOfSrc"]
  , body := (.ret
            (.mcall
              (.field (.name "this") "outerClass")
              "gson"
              [(.name "src"), (.name "typeOfSrc")])) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter$GsonContextImpl.deserialize:java.lang.Object(com.google.gson.JsonElement,java.lang.reflect.Type)`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter_GsonContextImpl_deserialize_java_lang_Object_com_google_gson_JsonElement : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter$GsonContextImpl.deserialize:java.lang.Object(com.google.gson.JsonElement,java.lang.reflect.Type)"
  , params := ["this", "json", "typeOfT"]
  , body := (.ret
            (.mcall (.field (.name "this") "outerClass") "gson" [(.name "json"), (.name "typeOfT")])) }

/-- `com.google.gson.internal.bind.TreeTypeAdapter$GsonContextImpl.<init>:void()`  (from `internal/bind/TreeTypeAdapter.java`) -/
def f_com_google_gson_internal_bind_TreeTypeAdapter_GsonContextImpl__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TreeTypeAdapter$GsonContextImpl.<init>:void()"
  , params := ["this", "outerClass"]
  , body := (.setField (.name "this") "outerClass" (.name "outerClass")) }

/-- `com.google.gson.internal.bind.TypeAdapterRuntimeTypeWrapper.<init>:void(com.google.gson.Gson,com.google.gson.TypeAdapter,java.lang.reflect.Type)`  (from `internal/bind/TypeAdapterRuntimeTypeWrapper.java`) -/
def f_com_google_gson_internal_bind_TypeAdapterRuntimeTypeWrapper__init__void_com_google_gson_Gson_com_google_gson_TypeAdapt : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapterRuntimeTypeWrapper.<init>:void(com.google.gson.Gson,com.google.gson.TypeAdapter,java.lang.reflect.Type)"
  , params := ["this", "context", "delegate", "type"]
  , body := (.seq
            (.setField (.name "this") "context" (.name "context"))
            (.seq
              (.setField (.name "this") "delegate" (.name "delegate"))
              (.setField (.name "this") "type" (.name "type")))) }

/-- `com.google.gson.internal.bind.TypeAdapterRuntimeTypeWrapper.read:java.lang.Object(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapterRuntimeTypeWrapper.java`) -/
def f_com_google_gson_internal_bind_TypeAdapterRuntimeTypeWrapper_read_java_lang_Object_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapterRuntimeTypeWrapper.read:java.lang.Object(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.ret (.mcall (.name "this") "delegate" [(.name "in")])) }

/-- `com.google.gson.internal.bind.TypeAdapterRuntimeTypeWrapper.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)`  (from `internal/bind/TypeAdapterRuntimeTypeWrapper.java`) -/
def f_com_google_gson_internal_bind_TypeAdapterRuntimeTypeWrapper_write_void_com_google_gson_stream_JsonWriter_java_lang_Obj : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapterRuntimeTypeWrapper.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)"
  , params := ["this", "out", "value"]
  , body := (.seq
            .skip
            (.seq
              (.assign "chosen" (.field (.name "this") "delegate"))
              (.seq
                .skip
                (.seq
                  (.assign
                    "runtimeType"
                    (.mcall (.name "this") "type" [(.field (.name "this") "type"), (.name "value")]))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "isDifferentType"
                        (.binop "!=" (.name "runtimeType") (.field (.name "this") "type")))
                      (.seq
                        (.ifte
                          (.name "isDifferentType")
                          (.seq
                            .skip
                            (.seq
                              (.assign "runtimeTypeAdapter" (.hole "op:cast"))
                              (.ifte
                                (.unop "!" (.hole "op:instanceOf"))
                                (.assign "chosen" (.name "runtimeTypeAdapter"))
                                (.ifte
                                  (.unop
                                    "!"
                                    (.call
                                      "com.google.gson.internal.bind.TypeAdapterRuntimeTypeWrapper.isReflective:boolean(com.google.gson.TypeAdapter)"
                                      [(.field (.name "this") "delegate")]))
                                  (.assign "chosen" (.field (.name "this") "delegate"))
                                  (.assign "chosen" (.name "runtimeTypeAdapter"))))))
                          .skip)
                        (.expr (.call "write" [(.name "out"), (.name "value")]))))))))) }

/-- `com.google.gson.internal.bind.TypeAdapterRuntimeTypeWrapper.isReflective:boolean(com.google.gson.TypeAdapter)`  (from `internal/bind/TypeAdapterRuntimeTypeWrapper.java`) -/
def f_com_google_gson_internal_bind_TypeAdapterRuntimeTypeWrapper_isReflective_boolean_com_google_gson_TypeAdapter_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapterRuntimeTypeWrapper.isReflective:boolean(com.google.gson.TypeAdapter)"
  , params := ["typeAdapter"]
  , body := (.seq
            (.loop
              (.hole "op:instanceOf")
              (.seq
                .skip
                (.seq
                  (.assign
                    "delegate"
                    (.call
                      "com.google.gson.internal.bind.SerializationDelegatingTypeAdapter.getSerializationDelegate:com.google.gson.TypeAdapter()"
                      []))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "hasNoDelegate"
                        (.binop "==" (.name "delegate") (.name "typeAdapter")))
                      (.seq
                        (.ifte (.name "hasNoDelegate") .brk .skip)
                        (.assign "typeAdapter" (.name "delegate"))))))))
            (.ret (.hole "op:instanceOf"))) }

/-- `com.google.gson.internal.bind.TypeAdapterRuntimeTypeWrapper.getRuntimeTypeIfMoreSpecific:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Object)`  (from `internal/bind/TypeAdapterRuntimeTypeWrapper.java`) -/
def f_com_google_gson_internal_bind_TypeAdapterRuntimeTypeWrapper_getRuntimeTypeIfMoreSpecific_java_lang_reflect_Type_java_l : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapterRuntimeTypeWrapper.getRuntimeTypeIfMoreSpecific:java.lang.reflect.Type(java.lang.reflect.Type,java.lang.Object)"
  , params := ["type", "value"]
  , body := (.seq
            (.ifte
              (.binop
                "&&"
                (.binop "!=" (.name "value") (.lit .unit))
                (.binop "||" (.hole "op:instanceOf") (.hole "op:instanceOf")))
              (.assign "type" (.call "getClass" []))
              .skip)
            (.ret (.name "type"))) }

/-- `com.google.gson.internal.bind.TypeAdapters.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.<init>:void()"
  , params := ["this"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.bind.TypeAdapters.atomicLongAdapter:com.google.gson.TypeAdapter(com.google.gson.TypeAdapter)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_atomicLongAdapter_com_google_gson_TypeAdapter_com_google_gson_TypeAdapter_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.atomicLongAdapter:com.google.gson.TypeAdapter(com.google.gson.TypeAdapter)"
  , params := ["longAdapter"]
  , body := (.seq
            (.expr (.call "requireNonNull" [(.name "longAdapter")]))
            (.ret (.call "nullSafe" []))) }

/-- `com.google.gson.internal.bind.TypeAdapters.atomicLongArrayAdapter:com.google.gson.TypeAdapter(com.google.gson.TypeAdapter)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_atomicLongArrayAdapter_com_google_gson_TypeAdapter_com_google_gson_TypeAdap : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.atomicLongArrayAdapter:com.google.gson.TypeAdapter(com.google.gson.TypeAdapter)"
  , params := ["longAdapter"]
  , body := (.seq
            (.expr (.call "requireNonNull" [(.name "longAdapter")]))
            (.ret (.call "nullSafe" []))) }

/-- `com.google.gson.internal.bind.TypeAdapters$FloatAdapter.<init>:void(boolean)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_FloatAdapter__init__void_boolean_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters$FloatAdapter.<init>:void(boolean)"
  , params := ["this", "strict"]
  , body := (.setField (.name "this") "strict" (.name "strict")) }

/-- `com.google.gson.internal.bind.TypeAdapters$FloatAdapter.read:java.lang.Float(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_FloatAdapter_read_java_lang_Float_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters$FloatAdapter.read:java.lang.Float(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.ret (.hole "op:cast"))) }

/-- `com.google.gson.internal.bind.TypeAdapters$FloatAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Number)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_FloatAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Number_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters$FloatAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Number)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "value") (.lit .unit))
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "floatValue" (.call "floatValue" []))
                (.seq
                  (.ifte
                    (.field (.name "this") "strict")
                    (.expr
                      (.call
                        "com.google.gson.internal.bind.TypeAdapters.checkValidFloatingPoint:void(double)"
                        [(.name "floatValue")]))
                    .skip)
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "floatNumber"
                        (.cond (.hole "op:instanceOf") (.name "value") (.name "floatValue")))
                      (.expr (.call "value" [(.name "floatNumber")])))))))) }

/-- `com.google.gson.internal.bind.TypeAdapters$DoubleAdapter.<init>:void(boolean)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_DoubleAdapter__init__void_boolean_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters$DoubleAdapter.<init>:void(boolean)"
  , params := ["this", "strict"]
  , body := (.setField (.name "this") "strict" (.name "strict")) }

/-- `com.google.gson.internal.bind.TypeAdapters$DoubleAdapter.read:java.lang.Double(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_DoubleAdapter_read_java_lang_Double_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters$DoubleAdapter.read:java.lang.Double(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.ret (.call "nextDouble" []))) }

/-- `com.google.gson.internal.bind.TypeAdapters$DoubleAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Number)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_DoubleAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Number : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters$DoubleAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Number)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "value") (.lit .unit))
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "doubleValue" (.call "doubleValue" []))
                (.seq
                  (.ifte
                    (.field (.name "this") "strict")
                    (.expr
                      (.call
                        "com.google.gson.internal.bind.TypeAdapters.checkValidFloatingPoint:void(double)"
                        [(.name "doubleValue")]))
                    .skip)
                  (.expr (.call "value" [(.name "doubleValue")])))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.checkValidFloatingPoint:void(double)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_checkValidFloatingPoint_void_double_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.checkValidFloatingPoint:void(double)"
  , params := ["value"]
  , body := (.ifte
            (.binop "||" (.call "isNaN" [(.name "value")]) (.call "isInfinite" [(.name "value")]))
            (.hole "control:THROW")
            .skip) }

/-- `com.google.gson.internal.bind.TypeAdapters$IntegerFieldsTypeAdapter.<init>:void(java.lang.String[])`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_IntegerFieldsTypeAdapter__init__void_java_lang_String___ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters$IntegerFieldsTypeAdapter.<init>:void(java.lang.String[])"
  , params := ["this", "fields"]
  , body := (.setField (.name "this") "fields" (.call "asList" [(.hole "op:arrayInitializer")])) }

/-- `com.google.gson.internal.bind.TypeAdapters$IntegerFieldsTypeAdapter.create:java.lang.Object(long[])`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_IntegerFieldsTypeAdapter_create_java_lang_Object_long___ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters$IntegerFieldsTypeAdapter.create:java.lang.Object(long[])"
  , params := ["this", "values"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters$IntegerFieldsTypeAdapter.integerValues:long[](java.lang.Object)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_IntegerFieldsTypeAdapter_integerValues_long___java_lang_Object_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters$IntegerFieldsTypeAdapter.integerValues:long[](java.lang.Object)"
  , params := ["this", "t"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters$IntegerFieldsTypeAdapter.read:java.lang.Object(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_IntegerFieldsTypeAdapter_read_java_lang_Object_com_google_gson_stream_JsonR : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters$IntegerFieldsTypeAdapter.read:java.lang.Object(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              (.expr (.call "beginObject" []))
              (.seq
                .skip
                (.seq
                  (.assign "values" (.hole "op:alloc"))
                  (.seq
                    (.loop
                      (.binop "!=" (.call "peek" []) (.field (.name "JsonToken") "END_OBJECT"))
                      (.seq
                        .skip
                        (.seq
                          (.assign "name" (.call "nextName" []))
                          (.seq
                            .skip
                            (.seq
                              (.assign "index" (.mcall (.name "this") "fields" [(.name "name")]))
                              (.ifte
                                (.binop ">=" (.name "index") (.lit (.int 0)))
                                (.setIndex (.name "values") (.name "index") (.call "nextLong" []))
                                (.expr (.call "skipValue" []))))))))
                    (.seq
                      (.expr (.call "endObject" []))
                      (.ret
                        (.call
                          "com.google.gson.internal.bind.TypeAdapters$IntegerFieldsTypeAdapter.create:java.lang.Object(long[])"
                          [(.name "values")])))))))) }

/-- `com.google.gson.internal.bind.TypeAdapters$IntegerFieldsTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_IntegerFieldsTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters$IntegerFieldsTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "value") (.lit .unit))
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              (.expr (.call "beginObject" []))
              (.seq
                .skip
                (.seq
                  (.assign
                    "values"
                    (.call
                      "com.google.gson.internal.bind.TypeAdapters$IntegerFieldsTypeAdapter.integerValues:long[](java.lang.Object)"
                      [(.name "value")]))
                  (.seq (.hole "control:FOR") (.expr (.call "endObject" []))))))) }

/-- `com.google.gson.internal.bind.TypeAdapters$FactorySupplier.get:com.google.gson.TypeAdapterFactory()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_FactorySupplier_get_com_google_gson_TypeAdapterFactory__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters$FactorySupplier.get:com.google.gson.TypeAdapterFactory()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.javaTimeTypeAdapterFactory:com.google.gson.TypeAdapterFactory()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_javaTimeTypeAdapterFactory_com_google_gson_TypeAdapterFactory__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.javaTimeTypeAdapterFactory:com.google.gson.TypeAdapterFactory()"
  , params := []
  , body := (.tryCatch
            (.seq
              .skip
              (.seq
                (.assign
                  "javaTimeTypeAdapterFactoryClass"
                  (.call
                    "forName"
                    [(.lit (.str "com.google.gson.internal.bind.JavaTimeTypeAdapters"))]))
                (.seq
                  .skip
                  (.seq
                    (.assign "supplier" (.hole "op:cast"))
                    (.ret
                      (.call
                        "com.google.gson.internal.bind.TypeAdapters$FactorySupplier.get:com.google.gson.TypeAdapterFactory()"
                        []))))))
            "__exc"
            (.ret (.lit .unit))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(com.google.gson.reflect.TypeToken,com.google.gson.TypeAdapter)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactory_com_google_gson_TypeAdapterFactory_com_google_gson_reflect_TypeT : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(com.google.gson.reflect.TypeToken,com.google.gson.TypeAdapter)"
  , params := ["type", "typeAdapter"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj42" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.<init>:void()"
                    [(.name "boxed"), (.name "typeAdapter"), (.name "unboxed")]))
                (.ret (.name "$obj42"))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactory_com_google_gson_TypeAdapterFactory_java_lang_Class_com_google_gs : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
  , params := ["type", "typeAdapter"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj43" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.<init>:void()"
                    [(.name "boxed"), (.name "typeAdapter"), (.name "unboxed")]))
                (.ret (.name "$obj43"))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,java.lang.Class,com.google.gson.TypeAdapter)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactory_com_google_gson_TypeAdapterFactory_java_lang_Class_java_lang_Cla : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,java.lang.Class,com.google.gson.TypeAdapter)"
  , params := ["unboxed", "boxed", "typeAdapter"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj44" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.<init>:void()"
                    [(.name "boxed"), (.name "typeAdapter"), (.name "unboxed")]))
                (.ret (.name "$obj44"))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactoryForMultipleTypes:com.google.gson.TypeAdapterFactory(java.lang.Class,java.lang.Class,com.google.gson.TypeAdapter)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactoryForMultipleTypes_com_google_gson_TypeAdapterFactory_java_lang_Cla : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactoryForMultipleTypes:com.google.gson.TypeAdapterFactory(java.lang.Class,java.lang.Class,com.google.gson.TypeAdapter)"
  , params := ["base", "sub", "typeAdapter"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj45" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.bind.TypeAdapters.newFactoryForMultipleTypes.TypeAdapterFactory$0.<init>:void()"
                    [(.name "base"), (.name "sub"), (.name "typeAdapter")]))
                (.ret (.name "$obj45"))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_com_google_gson_TypeAdapterFactory_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
  , params := ["clazz", "typeAdapter"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj46" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory.TypeAdapterFactory$0.<init>:void()"
                    [(.name "clazz"), (.name "typeAdapter")]))
                (.ret (.name "$obj46"))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_TypeAdapters__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.bind.TypeAdapters")
              "CLASS"
              (.call "nullSafe" []))
            (.seq
              (.setField
                (.fnref "com.google.gson.internal.bind.TypeAdapters")
                "CLASS_FACTORY"
                (.call
                  "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                  [ (.field (.name "Class") "class")
                  , (.field (.fnref "com.google.gson.internal.bind.TypeAdapters") "CLASS") ]))
              (.seq
                (.setField
                  (.fnref "com.google.gson.internal.bind.TypeAdapters")
                  "BIT_SET"
                  (.call "nullSafe" []))
                (.seq
                  (.setField
                    (.fnref "com.google.gson.internal.bind.TypeAdapters")
                    "BIT_SET_FACTORY"
                    (.call
                      "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                      [ (.field (.name "BitSet") "class")
                      , (.field (.fnref "com.google.gson.internal.bind.TypeAdapters") "BIT_SET") ]))
                  (.seq
                    (.setField
                      (.fnref "com.google.gson.internal.bind.TypeAdapters")
                      "BOOLEAN"
                      (.hole "op:alloc"))
                    (.seq
                      (.expr
                        (.mcall (.fnref "com.google.gson.internal.bind.TypeAdapters") "BOOLEAN" []))
                      (.seq
                        (.setField
                          (.fnref "com.google.gson.internal.bind.TypeAdapters")
                          "BOOLEAN_AS_STRING"
                          (.hole "op:alloc"))
                        (.seq
                          (.expr
                            (.mcall
                              (.fnref "com.google.gson.internal.bind.TypeAdapters")
                              "BOOLEAN_AS_STRING"
                              []))
                          (.seq
                            (.setField
                              (.fnref "com.google.gson.internal.bind.TypeAdapters")
                              "BOOLEAN_FACTORY"
                              (.call
                                "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,java.lang.Class,com.google.gson.TypeAdapter)"
                                [ (.field (.name "boolean") "class")
                                , (.field (.name "Boolean") "class")
                                , (.field
                                    (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                    "BOOLEAN") ]))
                            (.seq
                              (.setField
                                (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                "BYTE"
                                (.hole "op:alloc"))
                              (.seq
                                (.expr
                                  (.mcall
                                    (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                    "BYTE"
                                    []))
                                (.seq
                                  (.setField
                                    (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                    "BYTE_FACTORY"
                                    (.call
                                      "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,java.lang.Class,com.google.gson.TypeAdapter)"
                                      [ (.field (.name "byte") "class")
                                      , (.field (.name "Byte") "class")
                                      , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "BYTE") ]))
                                  (.seq
                                    (.setField
                                      (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                      "SHORT"
                                      (.hole "op:alloc"))
                                    (.seq
                                      (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "SHORT"
                                        []))
                                      (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "SHORT_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "short") "class")
                                        , (.field (.name "Short") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "SHORT") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "INTEGER"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "INTEGER"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "INTEGER_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "int") "class")
                                        , (.field (.name "Integer") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "INTEGER") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "ATOMIC_INTEGER"
                                        (.call "nullSafe" []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "ATOMIC_INTEGER_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "AtomicInteger") "class")
                                        , (.field (.name "TypeAdapters") "ATOMIC_INTEGER") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "ATOMIC_BOOLEAN"
                                        (.call "nullSafe" []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "ATOMIC_BOOLEAN_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "AtomicBoolean") "class")
                                        , (.field (.name "TypeAdapters") "ATOMIC_BOOLEAN") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "ATOMIC_INTEGER_ARRAY"
                                        (.call "nullSafe" []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "ATOMIC_INTEGER_ARRAY_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "AtomicIntegerArray") "class")
                                        , (.field (.name "TypeAdapters") "ATOMIC_INTEGER_ARRAY") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "LONG"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "LONG"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "LONG_AS_STRING"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "LONG_AS_STRING"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "FLOAT"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "FLOAT"
                                        [(.lit (.bool false))]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "FLOAT_STRICT"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "FLOAT_STRICT"
                                        [(.lit (.bool true))]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "DOUBLE"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "DOUBLE"
                                        [(.lit (.bool false))]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "DOUBLE_STRICT"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "DOUBLE_STRICT"
                                        [(.lit (.bool true))]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "CHARACTER"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "CHARACTER"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "CHARACTER_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "char") "class")
                                        , (.field (.name "Character") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "CHARACTER") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "STRING"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "STRING"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "BIG_DECIMAL"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "BIG_DECIMAL"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "BIG_DECIMAL_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "BigDecimal") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "BIG_DECIMAL") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "BIG_INTEGER"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "BIG_INTEGER"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "BIG_INTEGER_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "BigInteger") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "BIG_INTEGER") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "LAZILY_PARSED_NUMBER"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "LAZILY_PARSED_NUMBER"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "LAZILY_PARSED_NUMBER_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "LazilyParsedNumber") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "LAZILY_PARSED_NUMBER") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "STRING_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "String") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "STRING") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "STRING_BUILDER"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "STRING_BUILDER"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "STRING_BUILDER_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "StringBuilder") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "STRING_BUILDER") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "STRING_BUFFER"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "STRING_BUFFER"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "STRING_BUFFER_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "StringBuffer") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "STRING_BUFFER") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "URL"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "URL"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "URL_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "URL") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "URL") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "URI"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "URI"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "URI_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "URI") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "URI") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "INET_ADDRESS"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "INET_ADDRESS"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "INET_ADDRESS_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "InetAddress") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "INET_ADDRESS") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "UUID"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "UUID"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "UUID_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "UUID") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "UUID") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "CURRENCY"
                                        (.call "nullSafe" []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "CURRENCY_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "Currency") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "CURRENCY") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "CALENDAR"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "CALENDAR"
                                        [(.hole "op:arrayInitializer")]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "CALENDAR_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactoryForMultipleTypes:com.google.gson.TypeAdapterFactory(java.lang.Class,java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "Calendar") "class")
                                        , (.field (.name "GregorianCalendar") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "CALENDAR") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "LOCALE"
                                        (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "LOCALE"
                                        []))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "LOCALE_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "Locale") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "LOCALE") ]))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "JSON_ELEMENT"
                                        (.field (.name "JsonElementTypeAdapter") "ADAPTER"))
                                        (.seq
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "JSON_ELEMENT_FACTORY"
                                        (.call
                                        "com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory:com.google.gson.TypeAdapterFactory(java.lang.Class,com.google.gson.TypeAdapter)"
                                        [ (.field (.name "JsonElement") "class")
                                        , (.field
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "JSON_ELEMENT") ]))
                                        (.setField
                                        (.fnref "com.google.gson.internal.bind.TypeAdapters")
                                        "ENUM_FACTORY"
                                        (.field (.name "EnumTypeAdapter") "FACTORY"))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.CLASS.TypeAdapter$0.write:<unresolvedSignature>(2)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_CLASS_TypeAdapter_0_write__unresolvedSignature__2_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.CLASS.TypeAdapter$0.write:<unresolvedSignature>(2)"
  , params := ["this", "out", "value"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.bind.TypeAdapters.CLASS.TypeAdapter$0.read:<unresolvedSignature>(1)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_CLASS_TypeAdapter_0_read__unresolvedSignature__1_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.CLASS.TypeAdapter$0.read:<unresolvedSignature>(1)"
  , params := ["this", "in"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.bind.TypeAdapters.CLASS.TypeAdapter$0.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_CLASS_TypeAdapter_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.CLASS.TypeAdapter$0.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.BIT_SET.TypeAdapter$1.read:java.util.BitSet(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BIT_SET_TypeAdapter_1_read_java_util_BitSet_com_google_gson_stream_JsonRead : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BIT_SET.TypeAdapter$1.read:java.util.BitSet(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              (.assign "bitset" (.hole "op:alloc"))
              (.seq
                (.expr (.call "<init>" []))
                (.seq
                  (.expr (.call "beginArray" []))
                  (.seq
                    .skip
                    (.seq
                      (.assign "i" (.lit (.int 0)))
                      (.seq
                        .skip
                        (.seq
                          (.assign "tokenType" (.call "peek" []))
                          (.seq
                            (.loop
                              (.binop
                                "!="
                                (.name "tokenType")
                                (.field (.name "JsonToken") "END_ARRAY"))
                              (.seq
                                .skip
                                (.seq
                                  (.hole "control:SWITCH")
                                  (.seq
                                    (.ifte (.name "set") (.expr (.call "set" [(.name "i")])) .skip)
                                    (.seq
                                      (.expr (.hole "op:preIncrement"))
                                      (.assign "tokenType" (.call "peek" [])))))))
                            (.seq (.expr (.call "endArray" [])) (.ret (.name "bitset")))))))))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.BIT_SET.TypeAdapter$1.write:void(com.google.gson.stream.JsonWriter,java.util.BitSet)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BIT_SET_TypeAdapter_1_write_void_com_google_gson_stream_JsonWriter_java_uti : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BIT_SET.TypeAdapter$1.write:void(com.google.gson.stream.JsonWriter,java.util.BitSet)"
  , params := ["this", "out", "src"]
  , body := (.seq
            (.expr (.call "beginArray" []))
            (.seq (.hole "control:FOR") (.expr (.call "endArray" [])))) }

/-- `com.google.gson.internal.bind.TypeAdapters.BIT_SET.TypeAdapter$1.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BIT_SET_TypeAdapter_1__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BIT_SET.TypeAdapter$1.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.BOOLEAN.TypeAdapter$2.read:<unresolvedSignature>(1)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BOOLEAN_TypeAdapter_2_read__unresolvedSignature__1_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BOOLEAN.TypeAdapter$2.read:<unresolvedSignature>(1)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              (.assign "peek" (.call "peek" []))
              (.seq
                (.ifte
                  (.binop "==" (.name "peek") (.field (.name "JsonToken") "NULL"))
                  (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
                  (.ifte
                    (.binop "==" (.name "peek") (.field (.name "JsonToken") "STRING"))
                    (.ret (.call "parseBoolean" [(.call "nextString" [])]))
                    .skip))
                (.ret (.call "nextBoolean" []))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.BOOLEAN.TypeAdapter$2.write:<unresolvedSignature>(2)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BOOLEAN_TypeAdapter_2_write__unresolvedSignature__2_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BOOLEAN.TypeAdapter$2.write:<unresolvedSignature>(2)"
  , params := ["this", "out", "value"]
  , body := (.expr (.call "value" [(.name "value")])) }

/-- `com.google.gson.internal.bind.TypeAdapters.BOOLEAN.TypeAdapter$2.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BOOLEAN_TypeAdapter_2__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BOOLEAN.TypeAdapter$2.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.BOOLEAN_AS_STRING.TypeAdapter$3.read:<unresolvedSignature>(1)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BOOLEAN_AS_STRING_TypeAdapter_3_read__unresolvedSignature__1_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BOOLEAN_AS_STRING.TypeAdapter$3.read:<unresolvedSignature>(1)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.ret (.call "valueOf" [(.call "nextString" [])]))) }

/-- `com.google.gson.internal.bind.TypeAdapters.BOOLEAN_AS_STRING.TypeAdapter$3.write:<unresolvedSignature>(2)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BOOLEAN_AS_STRING_TypeAdapter_3_write__unresolvedSignature__2_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BOOLEAN_AS_STRING.TypeAdapter$3.write:<unresolvedSignature>(2)"
  , params := ["this", "out", "value"]
  , body := (.expr
            (.call
              "value"
              [ (.cond
                  (.binop "==" (.name "value") (.lit .unit))
                  (.lit (.str "null"))
                  (.call "toString" [])) ])) }

/-- `com.google.gson.internal.bind.TypeAdapters.BOOLEAN_AS_STRING.TypeAdapter$3.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BOOLEAN_AS_STRING_TypeAdapter_3__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BOOLEAN_AS_STRING.TypeAdapter$3.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.BYTE.TypeAdapter$4.read:<unresolvedSignature>(1)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BYTE_TypeAdapter_4_read__unresolvedSignature__1_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BYTE.TypeAdapter$4.read:<unresolvedSignature>(1)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.tryCatch
                  (.assign "intValue" (.call "nextInt" []))
                  "__exc"
                  (.hole "control:THROW"))
                (.seq
                  (.ifte
                    (.binop
                      "||"
                      (.binop ">" (.name "intValue") (.lit (.int 255)))
                      (.binop "<" (.name "intValue") (.field (.name "Byte") "MIN_VALUE")))
                    (.hole "control:THROW")
                    .skip)
                  (.ret (.hole "op:cast")))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.BYTE.TypeAdapter$4.write:<unresolvedSignature>(2)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BYTE_TypeAdapter_4_write__unresolvedSignature__2_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BYTE.TypeAdapter$4.write:<unresolvedSignature>(2)"
  , params := ["this", "out", "value"]
  , body := (.ifte
            (.binop "==" (.name "value") (.lit .unit))
            (.expr (.call "nullValue" []))
            (.expr (.call "value" [(.call "byteValue" [])]))) }

/-- `com.google.gson.internal.bind.TypeAdapters.BYTE.TypeAdapter$4.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BYTE_TypeAdapter_4__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BYTE.TypeAdapter$4.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.SHORT.TypeAdapter$5.read:<unresolvedSignature>(1)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_SHORT_TypeAdapter_5_read__unresolvedSignature__1_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.SHORT.TypeAdapter$5.read:<unresolvedSignature>(1)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.tryCatch
                  (.assign "intValue" (.call "nextInt" []))
                  "__exc"
                  (.hole "control:THROW"))
                (.seq
                  (.ifte
                    (.binop
                      "||"
                      (.binop ">" (.name "intValue") (.lit (.int 65535)))
                      (.binop "<" (.name "intValue") (.field (.name "Short") "MIN_VALUE")))
                    (.hole "control:THROW")
                    .skip)
                  (.ret (.hole "op:cast")))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.SHORT.TypeAdapter$5.write:<unresolvedSignature>(2)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_SHORT_TypeAdapter_5_write__unresolvedSignature__2_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.SHORT.TypeAdapter$5.write:<unresolvedSignature>(2)"
  , params := ["this", "out", "value"]
  , body := (.ifte
            (.binop "==" (.name "value") (.lit .unit))
            (.expr (.call "nullValue" []))
            (.expr (.call "value" [(.call "shortValue" [])]))) }

/-- `com.google.gson.internal.bind.TypeAdapters.SHORT.TypeAdapter$5.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_SHORT_TypeAdapter_5__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.SHORT.TypeAdapter$5.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.INTEGER.TypeAdapter$6.read:<unresolvedSignature>(1)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_INTEGER_TypeAdapter_6_read__unresolvedSignature__1_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.INTEGER.TypeAdapter$6.read:<unresolvedSignature>(1)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.tryCatch (.ret (.call "nextInt" [])) "__exc" (.hole "control:THROW"))) }

/-- `com.google.gson.internal.bind.TypeAdapters.INTEGER.TypeAdapter$6.write:<unresolvedSignature>(2)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_INTEGER_TypeAdapter_6_write__unresolvedSignature__2_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.INTEGER.TypeAdapter$6.write:<unresolvedSignature>(2)"
  , params := ["this", "out", "value"]
  , body := (.ifte
            (.binop "==" (.name "value") (.lit .unit))
            (.expr (.call "nullValue" []))
            (.expr (.call "value" [(.call "intValue" [])]))) }

/-- `com.google.gson.internal.bind.TypeAdapters.INTEGER.TypeAdapter$6.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_INTEGER_TypeAdapter_6__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.INTEGER.TypeAdapter$6.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.ATOMIC_INTEGER.TypeAdapter$7.read:java.util.concurrent.atomic.AtomicInteger(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_INTEGER_TypeAdapter_7_read_java_util_concurrent_atomic_AtomicInteger : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.ATOMIC_INTEGER.TypeAdapter$7.read:java.util.concurrent.atomic.AtomicInteger(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.tryCatch
            (.seq
              .skip
              (.seq
                (.assign "$obj12" (.hole "op:alloc"))
                (.seq (.expr (.call "<init>" [(.call "nextInt" [])])) (.ret (.name "$obj12")))))
            "__exc"
            (.hole "control:THROW")) }

/-- `com.google.gson.internal.bind.TypeAdapters.ATOMIC_INTEGER.TypeAdapter$7.write:void(com.google.gson.stream.JsonWriter,java.util.concurrent.atomic.AtomicInteger)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_INTEGER_TypeAdapter_7_write_void_com_google_gson_stream_JsonWriter_j : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.ATOMIC_INTEGER.TypeAdapter$7.write:void(com.google.gson.stream.JsonWriter,java.util.concurrent.atomic.AtomicInteger)"
  , params := ["this", "out", "value"]
  , body := (.expr (.call "value" [(.call "get" [])])) }

/-- `com.google.gson.internal.bind.TypeAdapters.ATOMIC_INTEGER.TypeAdapter$7.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_INTEGER_TypeAdapter_7__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.ATOMIC_INTEGER.TypeAdapter$7.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.ATOMIC_BOOLEAN.TypeAdapter$8.read:java.util.concurrent.atomic.AtomicBoolean(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_BOOLEAN_TypeAdapter_8_read_java_util_concurrent_atomic_AtomicBoolean : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.ATOMIC_BOOLEAN.TypeAdapter$8.read:java.util.concurrent.atomic.AtomicBoolean(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj15" (.hole "op:alloc"))
              (.seq (.expr (.call "<init>" [(.call "nextBoolean" [])])) (.ret (.name "$obj15"))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.ATOMIC_BOOLEAN.TypeAdapter$8.write:void(com.google.gson.stream.JsonWriter,java.util.concurrent.atomic.AtomicBoolean)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_BOOLEAN_TypeAdapter_8_write_void_com_google_gson_stream_JsonWriter_j : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.ATOMIC_BOOLEAN.TypeAdapter$8.write:void(com.google.gson.stream.JsonWriter,java.util.concurrent.atomic.AtomicBoolean)"
  , params := ["this", "out", "value"]
  , body := (.expr (.call "value" [(.call "get" [])])) }

/-- `com.google.gson.internal.bind.TypeAdapters.ATOMIC_BOOLEAN.TypeAdapter$8.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_BOOLEAN_TypeAdapter_8__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.ATOMIC_BOOLEAN.TypeAdapter$8.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.ATOMIC_INTEGER_ARRAY.TypeAdapter$9.read:java.util.concurrent.atomic.AtomicIntegerArray(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_INTEGER_ARRAY_TypeAdapter_9_read_java_util_concurrent_atomic_AtomicI : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.ATOMIC_INTEGER_ARRAY.TypeAdapter$9.read:java.util.concurrent.atomic.AtomicIntegerArray(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              (.assign "list" (.hole "op:alloc"))
              (.seq
                (.expr (.call "<init>" []))
                (.seq
                  (.expr (.call "beginArray" []))
                  (.seq
                    (.loop
                      (.call "hasNext" [])
                      (.tryCatch
                        (.seq
                          .skip
                          (.seq
                            (.assign "integer" (.call "nextInt" []))
                            (.expr (.call "add" [(.name "integer")]))))
                        "__exc"
                        (.hole "control:THROW")))
                    (.seq
                      (.expr (.call "endArray" []))
                      (.seq
                        .skip
                        (.seq
                          (.assign "length" (.call "size" []))
                          (.seq
                            .skip
                            (.seq
                              (.assign "array" (.hole "op:alloc"))
                              (.seq
                                (.expr (.call "<init>" [(.name "length")]))
                                (.seq (.hole "control:FOR") (.ret (.name "array")))))))))))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.ATOMIC_INTEGER_ARRAY.TypeAdapter$9.write:void(com.google.gson.stream.JsonWriter,java.util.concurrent.atomic.AtomicIntegerArray)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_INTEGER_ARRAY_TypeAdapter_9_write_void_com_google_gson_stream_JsonWr : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.ATOMIC_INTEGER_ARRAY.TypeAdapter$9.write:void(com.google.gson.stream.JsonWriter,java.util.concurrent.atomic.AtomicIntegerArray)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.expr (.call "beginArray" []))
            (.seq (.hole "control:FOR") (.expr (.call "endArray" [])))) }

/-- `com.google.gson.internal.bind.TypeAdapters.ATOMIC_INTEGER_ARRAY.TypeAdapter$9.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_INTEGER_ARRAY_TypeAdapter_9__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.ATOMIC_INTEGER_ARRAY.TypeAdapter$9.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.LONG.TypeAdapter$10.read:<unresolvedSignature>(1)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_LONG_TypeAdapter_10_read__unresolvedSignature__1_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.LONG.TypeAdapter$10.read:<unresolvedSignature>(1)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.tryCatch (.ret (.call "nextLong" [])) "__exc" (.hole "control:THROW"))) }

/-- `com.google.gson.internal.bind.TypeAdapters.LONG.TypeAdapter$10.write:<unresolvedSignature>(2)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_LONG_TypeAdapter_10_write__unresolvedSignature__2_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.LONG.TypeAdapter$10.write:<unresolvedSignature>(2)"
  , params := ["this", "out", "value"]
  , body := (.ifte
            (.binop "==" (.name "value") (.lit .unit))
            (.expr (.call "nullValue" []))
            (.expr (.call "value" [(.call "longValue" [])]))) }

/-- `com.google.gson.internal.bind.TypeAdapters.LONG.TypeAdapter$10.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_LONG_TypeAdapter_10__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.LONG.TypeAdapter$10.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.LONG_AS_STRING.TypeAdapter$11.read:<unresolvedSignature>(1)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_LONG_AS_STRING_TypeAdapter_11_read__unresolvedSignature__1_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.LONG_AS_STRING.TypeAdapter$11.read:<unresolvedSignature>(1)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.ret (.call "nextLong" []))) }

/-- `com.google.gson.internal.bind.TypeAdapters.LONG_AS_STRING.TypeAdapter$11.write:<unresolvedSignature>(2)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_LONG_AS_STRING_TypeAdapter_11_write__unresolvedSignature__2_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.LONG_AS_STRING.TypeAdapter$11.write:<unresolvedSignature>(2)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "value") (.lit .unit))
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.expr (.call "value" [(.call "toString" [])]))) }

/-- `com.google.gson.internal.bind.TypeAdapters.LONG_AS_STRING.TypeAdapter$11.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_LONG_AS_STRING_TypeAdapter_11__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.LONG_AS_STRING.TypeAdapter$11.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.CHARACTER.TypeAdapter$12.read:<unresolvedSignature>(1)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_CHARACTER_TypeAdapter_12_read__unresolvedSignature__1_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.CHARACTER.TypeAdapter$12.read:<unresolvedSignature>(1)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "str" (.call "nextString" []))
                (.seq
                  .skip
                  (.seq
                    (.assign "length" (.call "length" []))
                    (.seq
                      (.ifte
                        (.binop "!=" (.name "length") (.lit (.int 1)))
                        (.hole "control:THROW")
                        .skip)
                      (.ret (.call "charAt" [(.lit (.int 0))])))))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.CHARACTER.TypeAdapter$12.write:<unresolvedSignature>(2)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_CHARACTER_TypeAdapter_12_write__unresolvedSignature__2_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.CHARACTER.TypeAdapter$12.write:<unresolvedSignature>(2)"
  , params := ["this", "out", "value"]
  , body := (.expr
            (.call
              "value"
              [ (.cond
                  (.binop "==" (.name "value") (.lit .unit))
                  (.lit .unit)
                  (.call "valueOf" [(.name "value")])) ])) }

/-- `com.google.gson.internal.bind.TypeAdapters.CHARACTER.TypeAdapter$12.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_CHARACTER_TypeAdapter_12__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.CHARACTER.TypeAdapter$12.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.STRING.TypeAdapter$13.read:<unresolvedSignature>(1)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_STRING_TypeAdapter_13_read__unresolvedSignature__1_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.STRING.TypeAdapter$13.read:<unresolvedSignature>(1)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              (.assign "peek" (.call "peek" []))
              (.seq
                (.ifte
                  (.binop "==" (.name "peek") (.field (.name "JsonToken") "NULL"))
                  (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
                  .skip)
                (.seq
                  (.ifte
                    (.binop "==" (.name "peek") (.field (.name "JsonToken") "BOOLEAN"))
                    (.ret (.call "toString" [(.call "nextBoolean" [])]))
                    .skip)
                  (.ret (.call "nextString" [])))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.STRING.TypeAdapter$13.write:<unresolvedSignature>(2)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_STRING_TypeAdapter_13_write__unresolvedSignature__2_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.STRING.TypeAdapter$13.write:<unresolvedSignature>(2)"
  , params := ["this", "out", "value"]
  , body := (.expr (.call "value" [(.name "value")])) }

/-- `com.google.gson.internal.bind.TypeAdapters.STRING.TypeAdapter$13.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_STRING_TypeAdapter_13__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.STRING.TypeAdapter$13.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.BIG_DECIMAL.TypeAdapter$14.read:java.math.BigDecimal(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BIG_DECIMAL_TypeAdapter_14_read_java_math_BigDecimal_com_google_gson_stream : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BIG_DECIMAL.TypeAdapter$14.read:java.math.BigDecimal(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "s" (.call "nextString" []))
                (.tryCatch
                  (.ret
                    (.call
                      "com.google.gson.internal.NumberLimits.parseBigDecimal:java.math.BigDecimal(java.lang.String)"
                      [(.name "s")]))
                  "__exc"
                  (.hole "control:THROW"))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.BIG_DECIMAL.TypeAdapter$14.write:void(com.google.gson.stream.JsonWriter,java.math.BigDecimal)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BIG_DECIMAL_TypeAdapter_14_write_void_com_google_gson_stream_JsonWriter_jav : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BIG_DECIMAL.TypeAdapter$14.write:void(com.google.gson.stream.JsonWriter,java.math.BigDecimal)"
  , params := ["this", "out", "value"]
  , body := (.expr (.call "value" [(.name "value")])) }

/-- `com.google.gson.internal.bind.TypeAdapters.BIG_DECIMAL.TypeAdapter$14.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BIG_DECIMAL_TypeAdapter_14__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BIG_DECIMAL.TypeAdapter$14.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.BIG_INTEGER.TypeAdapter$15.read:java.math.BigInteger(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BIG_INTEGER_TypeAdapter_15_read_java_math_BigInteger_com_google_gson_stream : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BIG_INTEGER.TypeAdapter$15.read:java.math.BigInteger(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "s" (.call "nextString" []))
                (.tryCatch
                  (.ret
                    (.call
                      "com.google.gson.internal.NumberLimits.parseBigInteger:java.math.BigInteger(java.lang.String)"
                      [(.name "s")]))
                  "__exc"
                  (.hole "control:THROW"))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.BIG_INTEGER.TypeAdapter$15.write:void(com.google.gson.stream.JsonWriter,java.math.BigInteger)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BIG_INTEGER_TypeAdapter_15_write_void_com_google_gson_stream_JsonWriter_jav : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BIG_INTEGER.TypeAdapter$15.write:void(com.google.gson.stream.JsonWriter,java.math.BigInteger)"
  , params := ["this", "out", "value"]
  , body := (.expr (.call "value" [(.name "value")])) }

/-- `com.google.gson.internal.bind.TypeAdapters.BIG_INTEGER.TypeAdapter$15.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_BIG_INTEGER_TypeAdapter_15__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.BIG_INTEGER.TypeAdapter$15.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.LAZILY_PARSED_NUMBER.TypeAdapter$16.read:com.google.gson.internal.LazilyParsedNumber(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_LAZILY_PARSED_NUMBER_TypeAdapter_16_read_com_google_gson_internal_LazilyPar : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.LAZILY_PARSED_NUMBER.TypeAdapter$16.read:com.google.gson.internal.LazilyParsedNumber(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "$obj22" (.hole "op:alloc"))
                (.seq
                  (.expr
                    (.call
                      "com.google.gson.internal.LazilyParsedNumber.<init>:void(java.lang.String)"
                      [(.call "nextString" [])]))
                  (.ret (.name "$obj22")))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.LAZILY_PARSED_NUMBER.TypeAdapter$16.write:void(com.google.gson.stream.JsonWriter,com.google.gson.internal.LazilyParsedNumber)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_LAZILY_PARSED_NUMBER_TypeAdapter_16_write_void_com_google_gson_stream_JsonW : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.LAZILY_PARSED_NUMBER.TypeAdapter$16.write:void(com.google.gson.stream.JsonWriter,com.google.gson.internal.LazilyParsedNumber)"
  , params := ["this", "out", "value"]
  , body := (.expr (.call "value" [(.name "value")])) }

/-- `com.google.gson.internal.bind.TypeAdapters.LAZILY_PARSED_NUMBER.TypeAdapter$16.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_LAZILY_PARSED_NUMBER_TypeAdapter_16__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.LAZILY_PARSED_NUMBER.TypeAdapter$16.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.STRING_BUILDER.TypeAdapter$17.read:<unresolvedSignature>(1)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_STRING_BUILDER_TypeAdapter_17_read__unresolvedSignature__1_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.STRING_BUILDER.TypeAdapter$17.read:<unresolvedSignature>(1)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "$obj23" (.hole "op:alloc"))
                (.seq (.expr (.call "<init>" [(.call "nextString" [])])) (.ret (.name "$obj23")))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.STRING_BUILDER.TypeAdapter$17.write:<unresolvedSignature>(2)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_STRING_BUILDER_TypeAdapter_17_write__unresolvedSignature__2_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.STRING_BUILDER.TypeAdapter$17.write:<unresolvedSignature>(2)"
  , params := ["this", "out", "value"]
  , body := (.expr
            (.call
              "value"
              [ (.cond
                  (.binop "==" (.name "value") (.lit .unit))
                  (.lit .unit)
                  (.call "toString" [])) ])) }

/-- `com.google.gson.internal.bind.TypeAdapters.STRING_BUILDER.TypeAdapter$17.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_STRING_BUILDER_TypeAdapter_17__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.STRING_BUILDER.TypeAdapter$17.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.STRING_BUFFER.TypeAdapter$18.read:<unresolvedSignature>(1)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_STRING_BUFFER_TypeAdapter_18_read__unresolvedSignature__1_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.STRING_BUFFER.TypeAdapter$18.read:<unresolvedSignature>(1)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "$obj24" (.hole "op:alloc"))
                (.seq (.expr (.call "<init>" [(.call "nextString" [])])) (.ret (.name "$obj24")))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.STRING_BUFFER.TypeAdapter$18.write:<unresolvedSignature>(2)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_STRING_BUFFER_TypeAdapter_18_write__unresolvedSignature__2_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.STRING_BUFFER.TypeAdapter$18.write:<unresolvedSignature>(2)"
  , params := ["this", "out", "value"]
  , body := (.expr
            (.call
              "value"
              [ (.cond
                  (.binop "==" (.name "value") (.lit .unit))
                  (.lit .unit)
                  (.call "toString" [])) ])) }

/-- `com.google.gson.internal.bind.TypeAdapters.STRING_BUFFER.TypeAdapter$18.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_STRING_BUFFER_TypeAdapter_18__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.STRING_BUFFER.TypeAdapter$18.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.URL.TypeAdapter$19.read:java.net.URL(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_URL_TypeAdapter_19_read_java_net_URL_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.URL.TypeAdapter$19.read:java.net.URL(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "nextString" (.call "nextString" []))
                (.seq
                  (.ifte (.call "equals" [(.lit (.str "null"))]) (.ret (.lit .unit)) .skip)
                  (.tryCatch
                    (.seq
                      .skip
                      (.seq
                        (.assign "$obj25" (.hole "op:alloc"))
                        (.seq
                          (.expr (.call "<init>" [(.name "nextString")]))
                          (.ret (.name "$obj25")))))
                    "__exc"
                    (.hole "control:THROW")))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.URL.TypeAdapter$19.write:void(com.google.gson.stream.JsonWriter,java.net.URL)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_URL_TypeAdapter_19_write_void_com_google_gson_stream_JsonWriter_java_net_UR : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.URL.TypeAdapter$19.write:void(com.google.gson.stream.JsonWriter,java.net.URL)"
  , params := ["this", "out", "value"]
  , body := (.expr
            (.call
              "value"
              [ (.cond
                  (.binop "==" (.name "value") (.lit .unit))
                  (.lit .unit)
                  (.call "toExternalForm" [])) ])) }

/-- `com.google.gson.internal.bind.TypeAdapters.URL.TypeAdapter$19.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_URL_TypeAdapter_19__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.URL.TypeAdapter$19.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.URI.TypeAdapter$20.read:java.net.URI(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_URI_TypeAdapter_20_read_java_net_URI_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.URI.TypeAdapter$20.read:java.net.URI(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "nextString" (.call "nextString" []))
                (.seq
                  (.ifte (.call "equals" [(.lit (.str "null"))]) (.ret (.lit .unit)) .skip)
                  (.tryCatch
                    (.seq
                      .skip
                      (.seq
                        (.assign "$obj27" (.hole "op:alloc"))
                        (.seq
                          (.expr (.call "<init>" [(.name "nextString")]))
                          (.ret (.name "$obj27")))))
                    "__exc"
                    (.hole "control:THROW")))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.URI.TypeAdapter$20.write:void(com.google.gson.stream.JsonWriter,java.net.URI)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_URI_TypeAdapter_20_write_void_com_google_gson_stream_JsonWriter_java_net_UR : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.URI.TypeAdapter$20.write:void(com.google.gson.stream.JsonWriter,java.net.URI)"
  , params := ["this", "out", "value"]
  , body := (.expr
            (.call
              "value"
              [ (.cond
                  (.binop "==" (.name "value") (.lit .unit))
                  (.lit .unit)
                  (.call "toString" [])) ])) }

/-- `com.google.gson.internal.bind.TypeAdapters.URI.TypeAdapter$20.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_URI_TypeAdapter_20__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.URI.TypeAdapter$20.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.INET_ADDRESS.TypeAdapter$21.read:java.net.InetAddress(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_INET_ADDRESS_TypeAdapter_21_read_java_net_InetAddress_com_google_gson_strea : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.INET_ADDRESS.TypeAdapter$21.read:java.net.InetAddress(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "s" (.call "nextString" []))
                (.seq
                  (.ifte
                    (.binop
                      "&&"
                      (.unop "!" (.call "matches" []))
                      (.unop "!" (.call "getBoolean" [(.lit (.str "gson.allowDnsInetAddress"))])))
                    (.hole "control:THROW")
                    .skip)
                  (.seq
                    .skip
                    (.seq (.assign "addr" (.call "getByName" [(.name "s")])) (.ret (.name "addr")))))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.INET_ADDRESS.TypeAdapter$21.write:void(com.google.gson.stream.JsonWriter,java.net.InetAddress)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_INET_ADDRESS_TypeAdapter_21_write_void_com_google_gson_stream_JsonWriter_ja : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.INET_ADDRESS.TypeAdapter$21.write:void(com.google.gson.stream.JsonWriter,java.net.InetAddress)"
  , params := ["this", "out", "value"]
  , body := (.expr
            (.call
              "value"
              [ (.cond
                  (.binop "==" (.name "value") (.lit .unit))
                  (.lit .unit)
                  (.call "getHostAddress" [])) ])) }

/-- `com.google.gson.internal.bind.TypeAdapters.INET_ADDRESS.TypeAdapter$21.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_INET_ADDRESS_TypeAdapter_21__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.INET_ADDRESS.TypeAdapter$21.<init>:void()"
  , params := ["this"]
  , body := (.setField
            (.name "this")
            "ipAddressPattern"
            (.call "compile" [(.lit (.str ".*:.*|[0-9]+(\\\\.[0-9]+){3}"))])) }

/-- `com.google.gson.internal.bind.TypeAdapters.UUID.TypeAdapter$22.read:java.util.UUID(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_UUID_TypeAdapter_22_read_java_util_UUID_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.UUID.TypeAdapter$22.read:java.util.UUID(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "s" (.call "nextString" []))
                (.tryCatch
                  (.ret (.mcall (.field (.name "java") "util") "UUID" [(.name "s")]))
                  "__exc"
                  (.hole "control:THROW"))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.UUID.TypeAdapter$22.write:void(com.google.gson.stream.JsonWriter,java.util.UUID)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_UUID_TypeAdapter_22_write_void_com_google_gson_stream_JsonWriter_java_util_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.UUID.TypeAdapter$22.write:void(com.google.gson.stream.JsonWriter,java.util.UUID)"
  , params := ["this", "out", "value"]
  , body := (.expr
            (.call
              "value"
              [ (.cond
                  (.binop "==" (.name "value") (.lit .unit))
                  (.lit .unit)
                  (.call "toString" [])) ])) }

/-- `com.google.gson.internal.bind.TypeAdapters.UUID.TypeAdapter$22.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_UUID_TypeAdapter_22__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.UUID.TypeAdapter$22.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.CURRENCY.TypeAdapter$23.read:java.util.Currency(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_CURRENCY_TypeAdapter_23_read_java_util_Currency_com_google_gson_stream_Json : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.CURRENCY.TypeAdapter$23.read:java.util.Currency(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              (.assign "s" (.call "nextString" []))
              (.tryCatch (.ret (.call "getInstance" [(.name "s")])) "__exc" (.hole "control:THROW")))) }

/-- `com.google.gson.internal.bind.TypeAdapters.CURRENCY.TypeAdapter$23.write:void(com.google.gson.stream.JsonWriter,java.util.Currency)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_CURRENCY_TypeAdapter_23_write_void_com_google_gson_stream_JsonWriter_java_u : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.CURRENCY.TypeAdapter$23.write:void(com.google.gson.stream.JsonWriter,java.util.Currency)"
  , params := ["this", "out", "value"]
  , body := (.expr (.call "value" [(.call "getCurrencyCode" [])])) }

/-- `com.google.gson.internal.bind.TypeAdapters.CURRENCY.TypeAdapter$23.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_CURRENCY_TypeAdapter_23__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.CURRENCY.TypeAdapter$23.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.CALENDAR.IntegerFieldsTypeAdapter$24.create:java.util.Calendar(long[])`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_CALENDAR_IntegerFieldsTypeAdapter_24_create_java_util_Calendar_long___ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.CALENDAR.IntegerFieldsTypeAdapter$24.create:java.util.Calendar(long[])"
  , params := ["this", "values"]
  , body := (.seq
            .skip
            (.seq
              (.assign "$obj33" (.hole "op:alloc"))
              (.seq
                (.expr
                  (.call
                    "<init>"
                    [ (.call "toIntExact" [(.index (.name "values") (.lit (.int 0)))])
                    , (.call "toIntExact" [(.index (.name "values") (.lit (.int 1)))])
                    , (.call "toIntExact" [(.index (.name "values") (.lit (.int 2)))])
                    , (.call "toIntExact" [(.index (.name "values") (.lit (.int 3)))])
                    , (.call "toIntExact" [(.index (.name "values") (.lit (.int 4)))])
                    , (.call "toIntExact" [(.index (.name "values") (.lit (.int 5)))]) ]))
                (.ret (.name "$obj33"))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.CALENDAR.IntegerFieldsTypeAdapter$24.integerValues:long[](java.util.Calendar)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_CALENDAR_IntegerFieldsTypeAdapter_24_integerValues_long___java_util_Calenda : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.CALENDAR.IntegerFieldsTypeAdapter$24.integerValues:long[](java.util.Calendar)"
  , params := ["this", "calendar"]
  , body := (.ret (.hole "op:arrayInitializer")) }

/-- `com.google.gson.internal.bind.TypeAdapters.CALENDAR.IntegerFieldsTypeAdapter$24.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_CALENDAR_IntegerFieldsTypeAdapter_24__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.CALENDAR.IntegerFieldsTypeAdapter$24.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.LOCALE.TypeAdapter$25.read:java.util.Locale(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_LOCALE_TypeAdapter_25_read_java_util_Locale_com_google_gson_stream_JsonRead : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.LOCALE.TypeAdapter$25.read:java.util.Locale(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "locale" (.call "nextString" []))
                (.seq
                  .skip
                  (.seq
                    (.assign "tokenizer" (.hole "op:alloc"))
                    (.seq
                      (.expr (.call "<init>" [(.name "locale"), (.lit (.str "_"))]))
                      (.seq
                        .skip
                        (.seq
                          (.assign "language" (.lit .unit))
                          (.seq
                            .skip
                            (.seq
                              (.assign "country" (.lit .unit))
                              (.seq
                                .skip
                                (.seq
                                  (.assign "variant" (.lit .unit))
                                  (.seq
                                    (.ifte
                                      (.call "hasMoreElements" [])
                                      (.assign "language" (.call "nextToken" []))
                                      .skip)
                                    (.seq
                                      (.ifte
                                        (.call "hasMoreElements" [])
                                        (.assign "country" (.call "nextToken" []))
                                        .skip)
                                      (.seq
                                        (.ifte
                                        (.call "hasMoreElements" [])
                                        (.assign "variant" (.call "nextToken" []))
                                        .skip)
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.binop "==" (.name "country") (.lit .unit))
                                        (.binop "==" (.name "variant") (.lit .unit)))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "$obj34" (.hole "op:alloc"))
                                        (.seq
                                        (.expr (.call "<init>" [(.name "language")]))
                                        (.ret (.name "$obj34")))))
                                        (.ifte
                                        (.binop "==" (.name "variant") (.lit .unit))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "$obj35" (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.call "<init>" [(.name "language"), (.name "country")]))
                                        (.ret (.name "$obj35")))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "$obj36" (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "<init>"
                                        [(.name "language"), (.name "country"), (.name "variant")]))
                                        (.ret (.name "$obj36")))))))))))))))))))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.LOCALE.TypeAdapter$25.write:void(com.google.gson.stream.JsonWriter,java.util.Locale)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_LOCALE_TypeAdapter_25_write_void_com_google_gson_stream_JsonWriter_java_uti : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.LOCALE.TypeAdapter$25.write:void(com.google.gson.stream.JsonWriter,java.util.Locale)"
  , params := ["this", "out", "value"]
  , body := (.expr
            (.call
              "value"
              [ (.cond
                  (.binop "==" (.name "value") (.lit .unit))
                  (.lit .unit)
                  (.call "toString" [])) ])) }

/-- `com.google.gson.internal.bind.TypeAdapters.LOCALE.TypeAdapter$25.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_LOCALE_TypeAdapter_25__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.LOCALE.TypeAdapter$25.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.TypeAdapters.atomicLongAdapter.TypeAdapter$0.read:java.util.concurrent.atomic.AtomicLong(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_atomicLongAdapter_TypeAdapter_0_read_java_util_concurrent_atomic_AtomicLong : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.atomicLongAdapter.TypeAdapter$0.read:java.util.concurrent.atomic.AtomicLong(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              (.assign "value" (.mcall (.name "this") "longAdapter" [(.name "in")]))
              (.seq
                .skip
                (.seq
                  (.assign "$obj38" (.hole "op:alloc"))
                  (.seq (.expr (.call "<init>" [(.call "longValue" [])])) (.ret (.name "$obj38"))))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.atomicLongAdapter.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.util.concurrent.atomic.AtomicLong)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_atomicLongAdapter_TypeAdapter_0_write_void_com_google_gson_stream_JsonWrite : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.atomicLongAdapter.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.util.concurrent.atomic.AtomicLong)"
  , params := ["this", "out", "value"]
  , body := (.expr (.mcall (.name "this") "longAdapter" [(.name "out"), (.call "get" [])])) }

/-- `com.google.gson.internal.bind.TypeAdapters.atomicLongAdapter.TypeAdapter$0.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_atomicLongAdapter_TypeAdapter_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.atomicLongAdapter.TypeAdapter$0.<init>:void()"
  , params := ["this", "longAdapter"]
  , body := (.setField (.name "this") "longAdapter" (.name "longAdapter")) }

/-- `com.google.gson.internal.bind.TypeAdapters.atomicLongArrayAdapter.TypeAdapter$0.read:java.util.concurrent.atomic.AtomicLongArray(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_atomicLongArrayAdapter_TypeAdapter_0_read_java_util_concurrent_atomic_Atomi : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.atomicLongArrayAdapter.TypeAdapter$0.read:java.util.concurrent.atomic.AtomicLongArray(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              (.assign "list" (.hole "op:alloc"))
              (.seq
                (.expr (.call "<init>" []))
                (.seq
                  (.expr (.call "beginArray" []))
                  (.seq
                    (.loop
                      (.call "hasNext" [])
                      (.seq
                        .skip
                        (.seq
                          (.assign "value" (.mcall (.name "this") "longAdapter" [(.name "in")]))
                          (.seq
                            (.ifte
                              (.binop "==" (.name "value") (.lit .unit))
                              (.hole "control:THROW")
                              .skip)
                            (.expr (.call "add" [(.call "longValue" [])]))))))
                    (.seq
                      (.expr (.call "endArray" []))
                      (.seq
                        .skip
                        (.seq
                          (.assign "length" (.call "size" []))
                          (.seq
                            .skip
                            (.seq
                              (.assign "array" (.hole "op:alloc"))
                              (.seq
                                (.expr (.call "<init>" [(.name "length")]))
                                (.seq (.hole "control:FOR") (.ret (.name "array")))))))))))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.atomicLongArrayAdapter.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.util.concurrent.atomic.AtomicLongArray)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_atomicLongArrayAdapter_TypeAdapter_0_write_void_com_google_gson_stream_Json : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.atomicLongArrayAdapter.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.util.concurrent.atomic.AtomicLongArray)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.expr (.call "beginArray" []))
            (.seq (.hole "control:FOR") (.expr (.call "endArray" [])))) }

/-- `com.google.gson.internal.bind.TypeAdapters.atomicLongArrayAdapter.TypeAdapter$0.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_atomicLongArrayAdapter_TypeAdapter_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.atomicLongArrayAdapter.TypeAdapter$0.<init>:void()"
  , params := ["this", "longAdapter"]
  , body := (.setField (.name "this") "longAdapter" (.name "longAdapter")) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_goog : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.ret
            (.cond (.call "equals" [(.field (.name "this") "type")]) (.hole "op:cast") (.lit .unit))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.<init>:void()"
  , params := ["this", "type", "typeAdapter"]
  , body := (.seq
            (.setField (.name "this") "type" (.name "type"))
            (.setField (.name "this") "typeAdapter" (.name "typeAdapter"))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_goog' : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.ret
            (.cond
              (.binop "==" (.call "getRawType" []) (.field (.name "this") "type"))
              (.hole "op:cast")
              (.lit .unit))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.toString:<unresolvedSignature>(0)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0_toString__unresolvedSignature__0_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.toString:<unresolvedSignature>(0)"
  , params := ["this"]
  , body := (.ret
            (.binop
              "+"
              (.binop
                "+"
                (.binop
                  "+"
                  (.binop "+" (.lit (.str "Factory[type=")) (.mcall (.name "this") "type" []))
                  (.lit (.str ",adapter=")))
                (.field (.name "this") "typeAdapter"))
              (.lit (.str "]")))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0__init__void__' : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.<init>:void()"
  , params := ["this", "type", "typeAdapter"]
  , body := (.seq
            (.setField (.name "this") "type" (.name "type"))
            (.setField (.name "this") "typeAdapter" (.name "typeAdapter"))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_goog'' : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.seq
            .skip
            (.seq
              (.assign "rawType" (.call "getRawType" []))
              (.ret
                (.cond
                  (.binop
                    "||"
                    (.binop "==" (.name "rawType") (.field (.name "this") "unboxed"))
                    (.binop "==" (.name "rawType") (.field (.name "this") "boxed")))
                  (.hole "op:cast")
                  (.lit .unit))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.toString:<unresolvedSignature>(0)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0_toString__unresolvedSignature__0_' : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.toString:<unresolvedSignature>(0)"
  , params := ["this"]
  , body := (.ret
            (.binop
              "+"
              (.binop
                "+"
                (.binop
                  "+"
                  (.binop
                    "+"
                    (.binop
                      "+"
                      (.binop "+" (.lit (.str "Factory[type=")) (.mcall (.name "this") "boxed" []))
                      (.lit (.str "+")))
                    (.mcall (.name "this") "unboxed" []))
                  (.lit (.str ",adapter=")))
                (.field (.name "this") "typeAdapter"))
              (.lit (.str "]")))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0__init__void__'' : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactory.TypeAdapterFactory$0.<init>:void()"
  , params := ["this", "boxed", "typeAdapter", "unboxed"]
  , body := (.seq
            (.setField (.name "this") "boxed" (.name "boxed"))
            (.seq
              (.setField (.name "this") "typeAdapter" (.name "typeAdapter"))
              (.setField (.name "this") "unboxed" (.name "unboxed")))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactoryForMultipleTypes.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactoryForMultipleTypes_TypeAdapterFactory_0_create_com_google_gson_Type : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactoryForMultipleTypes.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.seq
            .skip
            (.seq
              (.assign "rawType" (.call "getRawType" []))
              (.ret
                (.cond
                  (.binop
                    "||"
                    (.binop "==" (.name "rawType") (.field (.name "this") "base"))
                    (.binop "==" (.name "rawType") (.field (.name "this") "sub")))
                  (.hole "op:cast")
                  (.lit .unit))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactoryForMultipleTypes.TypeAdapterFactory$0.toString:<unresolvedSignature>(0)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactoryForMultipleTypes_TypeAdapterFactory_0_toString__unresolvedSignatu : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactoryForMultipleTypes.TypeAdapterFactory$0.toString:<unresolvedSignature>(0)"
  , params := ["this"]
  , body := (.ret
            (.binop
              "+"
              (.binop
                "+"
                (.binop
                  "+"
                  (.binop
                    "+"
                    (.binop
                      "+"
                      (.binop "+" (.lit (.str "Factory[type=")) (.mcall (.name "this") "base" []))
                      (.lit (.str "+")))
                    (.mcall (.name "this") "sub" []))
                  (.lit (.str ",adapter=")))
                (.field (.name "this") "typeAdapter"))
              (.lit (.str "]")))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newFactoryForMultipleTypes.TypeAdapterFactory$0.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newFactoryForMultipleTypes_TypeAdapterFactory_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newFactoryForMultipleTypes.TypeAdapterFactory$0.<init>:void()"
  , params := ["this", "base", "sub", "typeAdapter"]
  , body := (.seq
            (.setField (.name "this") "base" (.name "base"))
            (.seq
              (.setField (.name "this") "sub" (.name "sub"))
              (.setField (.name "this") "typeAdapter" (.name "typeAdapter")))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_TypeAdapterFactory_0_create_com_google_gson_TypeAda : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.seq
            .skip
            (.seq
              (.assign "requestedType" (.call "getRawType" []))
              (.seq
                (.ifte
                  (.unop "!" (.mcall (.name "this") "clazz" [(.name "requestedType")]))
                  (.ret (.lit .unit))
                  .skip)
                (.ret (.hole "op:cast"))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory.TypeAdapterFactory$0.toString:<unresolvedSignature>(0)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_TypeAdapterFactory_0_toString__unresolvedSignature_ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory.TypeAdapterFactory$0.toString:<unresolvedSignature>(0)"
  , params := ["this"]
  , body := (.ret
            (.binop
              "+"
              (.binop
                "+"
                (.binop
                  "+"
                  (.binop
                    "+"
                    (.lit (.str "Factory[typeHierarchy="))
                    (.mcall (.name "this") "clazz" []))
                  (.lit (.str ",adapter=")))
                (.field (.name "this") "typeAdapter"))
              (.lit (.str "]")))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory.TypeAdapterFactory$0.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_TypeAdapterFactory_0__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory.TypeAdapterFactory$0.<init>:void()"
  , params := ["this", "clazz", "typeAdapter"]
  , body := (.seq
            (.setField (.name "this") "clazz" (.name "clazz"))
            (.setField (.name "this") "typeAdapter" (.name "typeAdapter"))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory.TypeAdapterFactory$0.create.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_TypeAdapterFactory_0_create_TypeAdapter_0_write_voi : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory.TypeAdapterFactory$0.create.TypeAdapter$0.write:void(com.google.gson.stream.JsonWriter,java.lang.Object)"
  , params := ["this", "out", "value"]
  , body := (.expr
            (.mcall
              (.field (.name "this") "outerClass")
              "typeAdapter"
              [(.name "out"), (.name "value")])) }

/-- `com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory.TypeAdapterFactory$0.create.TypeAdapter$0.read:java.lang.Object(com.google.gson.stream.JsonReader)`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_TypeAdapterFactory_0_create_TypeAdapter_0_read_java : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory.TypeAdapterFactory$0.create.TypeAdapter$0.read:java.lang.Object(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "result"
                (.mcall (.field (.name "this") "outerClass") "typeAdapter" [(.name "in")]))
              (.seq
                (.ifte
                  (.binop
                    "&&"
                    (.binop "!=" (.name "result") (.lit .unit))
                    (.unop "!" (.mcall (.name "this") "requestedType" [(.name "result")])))
                  (.hole "control:THROW")
                  .skip)
                (.ret (.name "result"))))) }

/-- `com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory.TypeAdapterFactory$0.create.TypeAdapter$0.<init>:void()`  (from `internal/bind/TypeAdapters.java`) -/
def f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_TypeAdapterFactory_0_create_TypeAdapter_0__init__vo : Func :=
  { name := "com.google.gson.internal.bind.TypeAdapters.newTypeHierarchyFactory.TypeAdapterFactory$0.create.TypeAdapter$0.<init>:void()"
  , params := ["this", "outerClass", "requestedType"]
  , body := (.seq
            (.setField (.name "this") "outerClass" (.name "outerClass"))
            (.setField (.name "this") "requestedType" (.name "requestedType"))) }

/-- `com.google.gson.internal.bind.util.ISO8601Utils.<init>:void()`  (from `internal/bind/util/ISO8601Utils.java`) -/
def f_com_google_gson_internal_bind_util_ISO8601Utils__init__void__ : Func :=
  { name := "com.google.gson.internal.bind.util.ISO8601Utils.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.bind.util.ISO8601Utils.format:java.lang.String(java.util.Date)`  (from `internal/bind/util/ISO8601Utils.java`) -/
def f_com_google_gson_internal_bind_util_ISO8601Utils_format_java_lang_String_java_util_Date_ : Func :=
  { name := "com.google.gson.internal.bind.util.ISO8601Utils.format:java.lang.String(java.util.Date)"
  , params := ["date"]
  , body := (.ret
            (.call
              "com.google.gson.internal.bind.util.ISO8601Utils.format:java.lang.String(java.util.Date,boolean,java.util.TimeZone)"
              [ (.name "date")
              , (.lit (.bool false))
              , (.field (.fnref "com.google.gson.internal.bind.util.ISO8601Utils") "TIMEZONE_UTC") ])) }

/-- `com.google.gson.internal.bind.util.ISO8601Utils.format:java.lang.String(java.util.Date,boolean)`  (from `internal/bind/util/ISO8601Utils.java`) -/
def f_com_google_gson_internal_bind_util_ISO8601Utils_format_java_lang_String_java_util_Date_boolean_ : Func :=
  { name := "com.google.gson.internal.bind.util.ISO8601Utils.format:java.lang.String(java.util.Date,boolean)"
  , params := ["date", "millis"]
  , body := (.ret
            (.call
              "com.google.gson.internal.bind.util.ISO8601Utils.format:java.lang.String(java.util.Date,boolean,java.util.TimeZone)"
              [ (.name "date")
              , (.name "millis")
              , (.field (.fnref "com.google.gson.internal.bind.util.ISO8601Utils") "TIMEZONE_UTC") ])) }

/-- `com.google.gson.internal.bind.util.ISO8601Utils.format:java.lang.String(java.util.Date,boolean,java.util.TimeZone)`  (from `internal/bind/util/ISO8601Utils.java`) -/
def f_com_google_gson_internal_bind_util_ISO8601Utils_format_java_lang_String_java_util_Date_boolean_java_util_TimeZone_ : Func :=
  { name := "com.google.gson.internal.bind.util.ISO8601Utils.format:java.lang.String(java.util.Date,boolean,java.util.TimeZone)"
  , params := ["date", "millis", "tz"]
  , body := (.seq
            .skip
            (.seq
              (.assign "calendar" (.hole "op:alloc"))
              (.seq
                (.expr (.call "<init>" [(.name "tz"), (.field (.name "Locale") "US")]))
                (.seq
                  (.expr (.call "setTime" [(.name "date")]))
                  (.seq
                    .skip
                    (.seq
                      (.assign "capacity" (.call "length" []))
                      (.seq
                        (.assign
                          "capacity"
                          (.binop
                            "+"
                            (.name "capacity")
                            (.cond (.name "millis") (.call "length" []) (.lit (.int 0)))))
                        (.seq
                          (.assign
                            "capacity"
                            (.binop
                              "+"
                              (.name "capacity")
                              (.cond
                                (.binop "==" (.call "getRawOffset" []) (.lit (.int 0)))
                                (.call "length" [])
                                (.call "length" []))))
                          (.seq
                            .skip
                            (.seq
                              (.assign "formatted" (.hole "op:alloc"))
                              (.seq
                                (.expr (.call "<init>" [(.name "capacity")]))
                                (.seq
                                  (.expr
                                    (.call
                                      "com.google.gson.internal.bind.util.ISO8601Utils.padInt:void(java.lang.StringBuilder,int,int)"
                                      [ (.name "formatted")
                                      , (.call "get" [(.field (.name "Calendar") "YEAR")])
                                      , (.call "length" []) ]))
                                  (.seq
                                    (.expr (.call "append" [(.lit (.str "-"))]))
                                    (.seq
                                      (.expr
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.padInt:void(java.lang.StringBuilder,int,int)"
                                        [ (.name "formatted")
                                        , (.binop
                                        "+"
                                        (.call "get" [(.field (.name "Calendar") "MONTH")])
                                        (.lit (.int 1)))
                                        , (.call "length" []) ]))
                                      (.seq
                                        (.expr (.call "append" [(.lit (.str "-"))]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.padInt:void(java.lang.StringBuilder,int,int)"
                                        [ (.name "formatted")
                                        , (.call "get" [(.field (.name "Calendar") "DAY_OF_MONTH")])
                                        , (.call "length" []) ]))
                                        (.seq
                                        (.expr (.call "append" [(.lit (.str "T"))]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.padInt:void(java.lang.StringBuilder,int,int)"
                                        [ (.name "formatted")
                                        , (.call "get" [(.field (.name "Calendar") "HOUR_OF_DAY")])
                                        , (.call "length" []) ]))
                                        (.seq
                                        (.expr (.call "append" [(.lit (.str ":"))]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.padInt:void(java.lang.StringBuilder,int,int)"
                                        [ (.name "formatted")
                                        , (.call "get" [(.field (.name "Calendar") "MINUTE")])
                                        , (.call "length" []) ]))
                                        (.seq
                                        (.expr (.call "append" [(.lit (.str ":"))]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.padInt:void(java.lang.StringBuilder,int,int)"
                                        [ (.name "formatted")
                                        , (.call "get" [(.field (.name "Calendar") "SECOND")])
                                        , (.call "length" []) ]))
                                        (.seq
                                        (.ifte
                                        (.name "millis")
                                        (.seq
                                        (.expr (.call "append" [(.lit (.str "."))]))
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.padInt:void(java.lang.StringBuilder,int,int)"
                                        [ (.name "formatted")
                                        , (.call "get" [(.field (.name "Calendar") "MILLISECOND")])
                                        , (.call "length" []) ])))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "offset"
                                        (.call "getOffset" [(.call "getTimeInMillis" [])]))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "offset") (.lit (.int 0)))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "hours"
                                        (.call
                                        "abs"
                                        [ (.binop
                                        "/"
                                        (.binop
                                        "/"
                                        (.name "offset")
                                        (.binop "*" (.lit (.int 60)) (.lit (.int 1000))))
                                        (.lit (.int 60))) ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "minutes"
                                        (.call
                                        "abs"
                                        [ (.binop
                                        "%"
                                        (.binop
                                        "/"
                                        (.name "offset")
                                        (.binop "*" (.lit (.int 60)) (.lit (.int 1000))))
                                        (.lit (.int 60))) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "append"
                                        [ (.cond
                                        (.binop "<" (.name "offset") (.lit (.int 0)))
                                        (.lit (.str "-"))
                                        (.lit (.str "+"))) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.padInt:void(java.lang.StringBuilder,int,int)"
                                        [(.name "formatted"), (.name "hours"), (.call "length" [])]))
                                        (.seq
                                        (.expr (.call "append" [(.lit (.str ":"))]))
                                        (.expr
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.padInt:void(java.lang.StringBuilder,int,int)"
                                        [ (.name "formatted")
                                        , (.name "minutes")
                                        , (.call "length" []) ])))))))))
                                        (.expr (.call "append" [(.lit (.str "Z"))])))
                                        (.ret (.call "toString" [])))))))))))))))))))))))))))) }

/-- `com.google.gson.internal.bind.util.ISO8601Utils.parse:java.util.Date(java.lang.String,java.text.ParsePosition)`  (from `internal/bind/util/ISO8601Utils.java`) -/
def f_com_google_gson_internal_bind_util_ISO8601Utils_parse_java_util_Date_java_lang_String_java_text_ParsePosition_ : Func :=
  { name := "com.google.gson.internal.bind.util.ISO8601Utils.parse:java.util.Date(java.lang.String,java.text.ParsePosition)"
  , params := ["date", "pos"]
  , body := (.seq
            .skip
            (.seq
              (.assign "fail" (.lit .unit))
              (.seq
                (.tryCatch
                  (.seq
                    .skip
                    (.seq
                      (.assign "offset" (.call "getIndex" []))
                      (.seq
                        .skip
                        (.seq
                          (.assign
                            "year"
                            (.call
                              "com.google.gson.internal.bind.util.ISO8601Utils.parseInt:int(java.lang.String,int,int)"
                              [(.name "date"), (.name "offset"), (.hole "op:assignmentPlus")]))
                          (.seq
                            (.ifte
                              (.call
                                "com.google.gson.internal.bind.util.ISO8601Utils.checkOffset:boolean(java.lang.String,int,char)"
                                [(.name "date"), (.name "offset"), (.lit (.str "-"))])
                              (.assign "offset" (.binop "+" (.name "offset") (.lit (.int 1))))
                              .skip)
                            (.seq
                              .skip
                              (.seq
                                (.assign
                                  "month"
                                  (.call
                                    "com.google.gson.internal.bind.util.ISO8601Utils.parseInt:int(java.lang.String,int,int)"
                                    [(.name "date"), (.name "offset"), (.hole "op:assignmentPlus")]))
                                (.seq
                                  (.ifte
                                    (.call
                                      "com.google.gson.internal.bind.util.ISO8601Utils.checkOffset:boolean(java.lang.String,int,char)"
                                      [(.name "date"), (.name "offset"), (.lit (.str "-"))])
                                    (.assign "offset" (.binop "+" (.name "offset") (.lit (.int 1))))
                                    .skip)
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign
                                        "day"
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.parseInt:int(java.lang.String,int,int)"
                                        [ (.name "date")
                                        , (.name "offset")
                                        , (.hole "op:assignmentPlus") ]))
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign "hour" (.lit (.int 0)))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "minutes" (.lit (.int 0)))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "seconds" (.lit (.int 0)))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "milliseconds" (.lit (.int 0)))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "hasT"
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.checkOffset:boolean(java.lang.String,int,char)"
                                        [(.name "date"), (.name "offset"), (.lit (.str "T"))]))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.unop "!" (.name "hasT"))
                                        (.binop "<=" (.call "length" []) (.name "offset")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "calendar" (.hole "op:alloc"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "<init>"
                                        [ (.name "year")
                                        , (.binop "-" (.name "month") (.lit (.int 1)))
                                        , (.name "day") ]))
                                        (.seq
                                        (.expr (.call "setLenient" [(.lit (.bool false))]))
                                        (.seq
                                        (.expr (.call "setIndex" [(.name "offset")]))
                                        (.ret (.call "getTime" [])))))))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.name "hasT")
                                        (.seq
                                        (.assign
                                        "hour"
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.parseInt:int(java.lang.String,int,int)"
                                        [ (.name "date")
                                        , (.hole "op:assignmentPlus")
                                        , (.hole "op:assignmentPlus") ]))
                                        (.seq
                                        (.ifte
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.checkOffset:boolean(java.lang.String,int,char)"
                                        [(.name "date"), (.name "offset"), (.lit (.str ":"))])
                                        (.assign
                                        "offset"
                                        (.binop "+" (.name "offset") (.lit (.int 1))))
                                        .skip)
                                        (.seq
                                        (.assign
                                        "minutes"
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.parseInt:int(java.lang.String,int,int)"
                                        [ (.name "date")
                                        , (.name "offset")
                                        , (.hole "op:assignmentPlus") ]))
                                        (.seq
                                        (.ifte
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.checkOffset:boolean(java.lang.String,int,char)"
                                        [(.name "date"), (.name "offset"), (.lit (.str ":"))])
                                        (.assign
                                        "offset"
                                        (.binop "+" (.name "offset") (.lit (.int 1))))
                                        .skip)
                                        (.ifte
                                        (.binop ">" (.call "length" []) (.name "offset"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "c" (.call "charAt" [(.name "offset")]))
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.binop
                                        "&&"
                                        (.binop "!=" (.name "c") (.lit (.str "Z")))
                                        (.binop "!=" (.name "c") (.lit (.str "+"))))
                                        (.binop "!=" (.name "c") (.lit (.str "-"))))
                                        (.seq
                                        (.assign
                                        "seconds"
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.parseInt:int(java.lang.String,int,int)"
                                        [ (.name "date")
                                        , (.name "offset")
                                        , (.hole "op:assignmentPlus") ]))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.binop ">" (.name "seconds") (.lit (.int 59)))
                                        (.binop "<" (.name "seconds") (.lit (.int 63))))
                                        (.assign "seconds" (.lit (.int 59)))
                                        .skip)
                                        (.ifte
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.checkOffset:boolean(java.lang.String,int,char)"
                                        [(.name "date"), (.name "offset"), (.lit (.str "."))])
                                        (.seq
                                        (.assign
                                        "offset"
                                        (.binop "+" (.name "offset") (.lit (.int 1))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "endOffset"
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.indexOfNonDigit:int(java.lang.String,int)"
                                        [ (.name "date")
                                        , (.binop "+" (.name "offset") (.lit (.int 1))) ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "parseEndOffset"
                                        (.call
                                        "min"
                                        [ (.name "endOffset")
                                        , (.binop "+" (.name "offset") (.lit (.int 3))) ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "fraction"
                                        (.call
                                        "com.google.gson.internal.bind.util.ISO8601Utils.parseInt:int(java.lang.String,int,int)"
                                        [(.name "date"), (.name "offset"), (.name "parseEndOffset")]))
                                        (.seq
                                        (.hole "control:SWITCH")
                                        (.assign "offset" (.name "endOffset"))))))))))
                                        .skip)))
                                        .skip)))
                                        .skip)))))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.binop "<=" (.call "length" []) (.name "offset"))
                                        (.hole "control:THROW")
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "timezone" (.lit .unit))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "timezoneIndicator"
                                        (.call "charAt" [(.name "offset")]))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "timezoneIndicator") (.lit (.str "Z")))
                                        (.seq
                                        (.assign
                                        "timezone"
                                        (.field
                                        (.fnref "com.google.gson.internal.bind.util.ISO8601Utils")
                                        "TIMEZONE_UTC"))
                                        (.assign
                                        "offset"
                                        (.binop "+" (.name "offset") (.lit (.int 1)))))
                                        (.ifte
                                        (.binop
                                        "||"
                                        (.binop "==" (.name "timezoneIndicator") (.lit (.str "+")))
                                        (.binop "==" (.name "timezoneIndicator") (.lit (.str "-"))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "timezoneOffset"
                                        (.call "substring" [(.name "offset")]))
                                        (.seq
                                        (.assign
                                        "timezoneOffset"
                                        (.cond
                                        (.binop ">=" (.call "length" []) (.lit (.int 5)))
                                        (.name "timezoneOffset")
                                        (.binop "+" (.name "timezoneOffset") (.lit (.str "00")))))
                                        (.seq
                                        (.assign
                                        "offset"
                                        (.binop "+" (.name "offset") (.call "length" [])))
                                        (.ifte
                                        (.binop
                                        "||"
                                        (.call "equals" [(.lit (.str "+0000"))])
                                        (.call "equals" [(.lit (.str "+00:00"))]))
                                        (.assign
                                        "timezone"
                                        (.field
                                        (.fnref "com.google.gson.internal.bind.util.ISO8601Utils")
                                        "TIMEZONE_UTC"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "timezoneId"
                                        (.binop "+" (.lit (.str "GMT")) (.name "timezoneOffset")))
                                        (.seq
                                        (.assign
                                        "timezone"
                                        (.call "getTimeZone" [(.name "timezoneId")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "act" (.call "getID" []))
                                        (.ifte
                                        (.unop "!" (.call "equals" [(.name "timezoneId")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "cleaned"
                                        (.call "replace" [(.lit (.str ":")), (.lit (.str ""))]))
                                        (.ifte
                                        (.unop "!" (.call "equals" [(.name "timezoneId")]))
                                        (.hole "control:THROW")
                                        .skip)))
                                        .skip)))))))))))
                                        (.hole "control:THROW")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "calendar" (.hole "op:alloc"))
                                        (.seq
                                        (.expr (.call "<init>" [(.name "timezone")]))
                                        (.seq
                                        (.expr (.call "setLenient" [(.lit (.bool false))]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "set"
                                        [(.field (.name "Calendar") "YEAR"), (.name "year")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "set"
                                        [ (.field (.name "Calendar") "MONTH")
                                        , (.binop "-" (.name "month") (.lit (.int 1))) ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "set"
                                        [(.field (.name "Calendar") "DAY_OF_MONTH"), (.name "day")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "set"
                                        [(.field (.name "Calendar") "HOUR_OF_DAY"), (.name "hour")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "set"
                                        [(.field (.name "Calendar") "MINUTE"), (.name "minutes")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "set"
                                        [(.field (.name "Calendar") "SECOND"), (.name "seconds")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "set"
                                        [ (.field (.name "Calendar") "MILLISECOND")
                                        , (.name "milliseconds") ]))
                                        (.seq
                                        (.expr (.call "setIndex" [(.name "offset")]))
                                        (.ret (.call "getTime" []))))))))))))))))))))))))))))))))))))))))))
                  "__exc"
                  (.assign "fail" (.name "e")))
                (.seq
                  .skip
                  (.seq
                    (.assign
                      "input"
                      (.cond
                        (.binop "==" (.name "date") (.lit .unit))
                        (.lit .unit)
                        (.binop
                          "+"
                          (.binop "+" (.lit (.str "\"")) (.name "date"))
                          (.lit (.str "\"")))))
                    (.seq
                      .skip
                      (.seq
                        (.assign "msg" (.call "getMessage" []))
                        (.seq
                          (.ifte
                            (.binop
                              "||"
                              (.binop "==" (.name "msg") (.lit .unit))
                              (.call "isEmpty" []))
                            (.assign
                              "msg"
                              (.binop
                                "+"
                                (.binop "+" (.lit (.str "(")) (.call "getName" []))
                                (.lit (.str ")"))))
                            .skip)
                          (.seq
                            .skip
                            (.seq
                              (.assign "ex" (.hole "op:alloc"))
                              (.seq
                                (.expr
                                  (.call
                                    "<init>"
                                    [ (.binop
                                        "+"
                                        (.binop
                                        "+"
                                        (.binop
                                        "+"
                                        (.lit (.str "Failed to parse date ["))
                                        (.name "input"))
                                        (.lit (.str "]: ")))
                                        (.name "msg"))
                                    , (.call "getIndex" []) ]))
                                (.seq
                                  (.expr (.call "initCause" [(.name "fail")]))
                                  (.hole "control:THROW"))))))))))))) }

/-- `com.google.gson.internal.bind.util.ISO8601Utils.checkOffset:boolean(java.lang.String,int,char)`  (from `internal/bind/util/ISO8601Utils.java`) -/
def f_com_google_gson_internal_bind_util_ISO8601Utils_checkOffset_boolean_java_lang_String_int_char_ : Func :=
  { name := "com.google.gson.internal.bind.util.ISO8601Utils.checkOffset:boolean(java.lang.String,int,char)"
  , params := ["value", "offset", "expected"]
  , body := (.ret
            (.binop
              "&&"
              (.binop "<" (.name "offset") (.call "length" []))
              (.binop "==" (.call "charAt" [(.name "offset")]) (.name "expected")))) }

/-- `com.google.gson.internal.bind.util.ISO8601Utils.parseInt:int(java.lang.String,int,int)`  (from `internal/bind/util/ISO8601Utils.java`) -/
def f_com_google_gson_internal_bind_util_ISO8601Utils_parseInt_int_java_lang_String_int_int_ : Func :=
  { name := "com.google.gson.internal.bind.util.ISO8601Utils.parseInt:int(java.lang.String,int,int)"
  , params := ["value", "beginIndex", "endIndex"]
  , body := (.seq
            (.ifte
              (.binop
                "||"
                (.binop
                  "||"
                  (.binop "<" (.name "beginIndex") (.lit (.int 0)))
                  (.binop ">" (.name "endIndex") (.call "length" [])))
                (.binop ">" (.name "beginIndex") (.name "endIndex")))
              (.hole "control:THROW")
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "i" (.name "beginIndex"))
                (.seq
                  .skip
                  (.seq
                    (.assign "result" (.lit (.int 0)))
                    (.seq
                      .skip
                      (.seq
                        (.ifte
                          (.binop "<" (.name "i") (.name "endIndex"))
                          (.seq
                            (.assign
                              "digit"
                              (.call
                                "digit"
                                [(.call "charAt" [(.hole "op:postIncrement")]), (.lit (.int 10))]))
                            (.seq
                              (.ifte
                                (.binop "<" (.name "digit") (.lit (.int 0)))
                                (.hole "control:THROW")
                                .skip)
                              (.assign "result" (.unop "-" (.name "digit")))))
                          .skip)
                        (.seq
                          (.loop
                            (.binop "<" (.name "i") (.name "endIndex"))
                            (.seq
                              (.assign
                                "digit"
                                (.call
                                  "digit"
                                  [(.call "charAt" [(.hole "op:postIncrement")]), (.lit (.int 10))]))
                              (.seq
                                (.ifte
                                  (.binop "<" (.name "digit") (.lit (.int 0)))
                                  (.hole "control:THROW")
                                  .skip)
                                (.seq
                                  (.expr (.hole "op:assignmentMultiplication"))
                                  (.assign "result" (.binop "-" (.name "result") (.name "digit")))))))
                          (.ret (.unop "-" (.name "result"))))))))))) }

/-- `com.google.gson.internal.bind.util.ISO8601Utils.padInt:void(java.lang.StringBuilder,int,int)`  (from `internal/bind/util/ISO8601Utils.java`) -/
def f_com_google_gson_internal_bind_util_ISO8601Utils_padInt_void_java_lang_StringBuilder_int_int_ : Func :=
  { name := "com.google.gson.internal.bind.util.ISO8601Utils.padInt:void(java.lang.StringBuilder,int,int)"
  , params := ["buffer", "value", "length"]
  , body := (.seq
            .skip
            (.seq
              (.assign "strValue" (.call "toString" [(.name "value")]))
              (.seq (.hole "control:FOR") (.expr (.call "append" [(.name "strValue")]))))) }

/-- `com.google.gson.internal.bind.util.ISO8601Utils.indexOfNonDigit:int(java.lang.String,int)`  (from `internal/bind/util/ISO8601Utils.java`) -/
def f_com_google_gson_internal_bind_util_ISO8601Utils_indexOfNonDigit_int_java_lang_String_int_ : Func :=
  { name := "com.google.gson.internal.bind.util.ISO8601Utils.indexOfNonDigit:int(java.lang.String,int)"
  , params := ["string", "offset"]
  , body := (.seq (.hole "control:FOR") (.ret (.call "length" []))) }

/-- `com.google.gson.internal.bind.util.ISO8601Utils.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_bind_util_ISO8601Utils__clinit__void__ : Func :=
  { name := "com.google.gson.internal.bind.util.ISO8601Utils.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.bind.util.ISO8601Utils")
              "UTC_ID"
              (.lit (.str "UTC")))
            (.setField
              (.fnref "com.google.gson.internal.bind.util.ISO8601Utils")
              "TIMEZONE_UTC"
              (.call
                "getTimeZone"
                [(.field (.fnref "com.google.gson.internal.bind.util.ISO8601Utils") "UTC_ID")]))) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.<init>:void()`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper__init__void__ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.reflect.ReflectionHelper.getInaccessibleTroubleshootingSuffix:java.lang.String(java.lang.Exception)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_getInaccessibleTroubleshootingSuffix_java_lang_String_java_lang_Exce : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.getInaccessibleTroubleshootingSuffix:java.lang.String(java.lang.Exception)"
  , params := ["e"]
  , body := (.seq
            (.ifte
              (.call "equals" [(.lit (.str "java.lang.reflect.InaccessibleObjectException"))])
              (.seq
                .skip
                (.seq
                  (.assign "message" (.call "getMessage" []))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "troubleshootingId"
                        (.cond
                          (.binop
                            "&&"
                            (.binop "!=" (.name "message") (.lit .unit))
                            (.call "contains" [(.lit (.str "to module com.google.gson"))]))
                          (.lit (.str "reflection-inaccessible-to-module-gson"))
                          (.lit (.str "reflection-inaccessible"))))
                      (.ret
                        (.binop
                          "+"
                          (.lit (.str "\\nSee "))
                          (.call
                            "com.google.gson.internal.TroubleshootingGuide.createUrl:java.lang.String(java.lang.String)"
                            [(.name "troubleshootingId")])))))))
              .skip)
            (.ret (.lit (.str "")))) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.makeAccessible:void(java.lang.reflect.AccessibleObject)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_makeAccessible_void_java_lang_reflect_AccessibleObject_ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.makeAccessible:void(java.lang.reflect.AccessibleObject)"
  , params := ["object"]
  , body := (.tryCatch
            (.expr (.call "setAccessible" [(.lit (.bool true))]))
            "__exc"
            (.seq
              .skip
              (.seq
                (.assign
                  "description"
                  (.call
                    "com.google.gson.internal.reflect.ReflectionHelper.getAccessibleObjectDescription:java.lang.String(java.lang.reflect.AccessibleObject,boolean)"
                    [(.name "object"), (.lit (.bool false))]))
                (.hole "control:THROW")))) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.getAccessibleObjectDescription:java.lang.String(java.lang.reflect.AccessibleObject,boolean)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_getAccessibleObjectDescription_java_lang_String_java_lang_reflect_Ac : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.getAccessibleObjectDescription:java.lang.String(java.lang.reflect.AccessibleObject,boolean)"
  , params := ["object", "uppercaseFirstLetter"]
  , body := (.seq
            .skip
            (.seq
              (.ifte
                (.hole "op:instanceOf")
                (.assign
                  "description"
                  (.binop
                    "+"
                    (.binop
                      "+"
                      (.lit (.str "field '"))
                      (.call
                        "com.google.gson.internal.reflect.ReflectionHelper.fieldToString:java.lang.String(java.lang.reflect.Field)"
                        [(.hole "op:cast")]))
                    (.lit (.str "'"))))
                (.ifte
                  (.hole "op:instanceOf")
                  (.seq
                    .skip
                    (.seq
                      (.assign "method" (.hole "op:cast"))
                      (.seq
                        .skip
                        (.seq
                          (.assign "methodSignatureBuilder" (.hole "op:alloc"))
                          (.seq
                            (.expr (.call "<init>" [(.call "getName" [])]))
                            (.seq
                              (.expr
                                (.call
                                  "com.google.gson.internal.reflect.ReflectionHelper.appendExecutableParameters:void(java.lang.reflect.AccessibleObject,java.lang.StringBuilder)"
                                  [(.name "method"), (.name "methodSignatureBuilder")]))
                              (.seq
                                .skip
                                (.seq
                                  (.assign "methodSignature" (.call "toString" []))
                                  (.assign
                                    "description"
                                    (.binop
                                      "+"
                                      (.binop
                                        "+"
                                        (.binop
                                        "+"
                                        (.binop "+" (.lit (.str "method '")) (.call "getName" []))
                                        (.lit (.str "#")))
                                        (.name "methodSignature"))
                                      (.lit (.str "'"))))))))))))
                  (.ifte
                    (.hole "op:instanceOf")
                    (.assign
                      "description"
                      (.binop
                        "+"
                        (.binop
                          "+"
                          (.lit (.str "constructor '"))
                          (.call
                            "com.google.gson.internal.reflect.ReflectionHelper.constructorToString:java.lang.String(java.lang.reflect.Constructor)"
                            [(.hole "op:cast")]))
                        (.lit (.str "'"))))
                    (.assign
                      "description"
                      (.binop "+" (.lit (.str "<unknown AccessibleObject> ")) (.call "toString" []))))))
              (.seq
                (.ifte
                  (.binop
                    "&&"
                    (.name "uppercaseFirstLetter")
                    (.call "isLowerCase" [(.call "charAt" [(.lit (.int 0))])]))
                  (.assign
                    "description"
                    (.binop
                      "+"
                      (.call "toUpperCase" [(.call "charAt" [(.lit (.int 0))])])
                      (.call "substring" [(.lit (.int 1))])))
                  .skip)
                (.ret (.name "description"))))) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.fieldToString:java.lang.String(java.lang.reflect.Field)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_fieldToString_java_lang_String_java_lang_reflect_Field_ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.fieldToString:java.lang.String(java.lang.reflect.Field)"
  , params := ["field"]
  , body := (.ret
            (.binop "+" (.binop "+" (.call "getName" []) (.lit (.str "#"))) (.call "getName" []))) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.constructorToString:java.lang.String(java.lang.reflect.Constructor)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_constructorToString_java_lang_String_java_lang_reflect_Constructor_ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.constructorToString:java.lang.String(java.lang.reflect.Constructor)"
  , params := ["constructor"]
  , body := (.seq
            .skip
            (.seq
              (.assign "stringBuilder" (.hole "op:alloc"))
              (.seq
                (.expr (.call "<init>" [(.call "getName" [])]))
                (.seq
                  (.expr
                    (.call
                      "com.google.gson.internal.reflect.ReflectionHelper.appendExecutableParameters:void(java.lang.reflect.AccessibleObject,java.lang.StringBuilder)"
                      [(.name "constructor"), (.name "stringBuilder")]))
                  (.ret (.call "toString" [])))))) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.appendExecutableParameters:void(java.lang.reflect.AccessibleObject,java.lang.StringBuilder)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_appendExecutableParameters_void_java_lang_reflect_AccessibleObject_j : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.appendExecutableParameters:void(java.lang.reflect.AccessibleObject,java.lang.StringBuilder)"
  , params := ["executable", "stringBuilder"]
  , body := (.seq
            (.expr (.call "append" [(.lit (.str "("))]))
            (.seq
              .skip
              (.seq
                (.assign
                  "parameters"
                  (.cond
                    (.hole "op:instanceOf")
                    (.call "getParameterTypes" [])
                    (.call "getParameterTypes" [])))
                (.seq (.hole "control:FOR") (.expr (.call "append" [(.lit (.str ")"))])))))) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.isStatic:boolean(java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_isStatic_boolean_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.isStatic:boolean(java.lang.Class)"
  , params := ["clazz"]
  , body := (.ret (.call "isStatic" [(.call "getModifiers" [])])) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.isAnonymousOrNonStaticLocal:boolean(java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_isAnonymousOrNonStaticLocal_boolean_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.isAnonymousOrNonStaticLocal:boolean(java.lang.Class)"
  , params := ["clazz"]
  , body := (.ret
            (.binop
              "&&"
              (.unop
                "!"
                (.call
                  "com.google.gson.internal.reflect.ReflectionHelper.isStatic:boolean(java.lang.Class)"
                  [(.name "clazz")]))
              (.binop "||" (.call "isAnonymousClass" []) (.call "isLocalClass" [])))) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.tryMakeAccessible:java.lang.String(java.lang.reflect.Constructor)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_tryMakeAccessible_java_lang_String_java_lang_reflect_Constructor_ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.tryMakeAccessible:java.lang.String(java.lang.reflect.Constructor)"
  , params := ["constructor"]
  , body := (.tryCatch
            (.seq (.expr (.call "setAccessible" [(.lit (.bool true))])) (.ret (.lit .unit)))
            "__exc"
            (.ret
              (.binop
                "+"
                (.binop
                  "+"
                  (.binop
                    "+"
                    (.binop
                      "+"
                      (.binop
                        "+"
                        (.lit (.str "Failed making constructor '"))
                        (.call
                          "com.google.gson.internal.reflect.ReflectionHelper.constructorToString:java.lang.String(java.lang.reflect.Constructor)"
                          [(.name "constructor")]))
                      (.lit
                        (.str "' accessible; either increase its visibility or write a custom InstanceCreator or")))
                    (.lit (.str " TypeAdapter for its declaring type: ")))
                  (.call "getMessage" []))
                (.call
                  "com.google.gson.internal.reflect.ReflectionHelper.getInaccessibleTroubleshootingSuffix:java.lang.String(java.lang.Exception)"
                  [(.name "exception")])))) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.isRecord:boolean(java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_isRecord_boolean_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.isRecord:boolean(java.lang.Class)"
  , params := ["raw"]
  , body := (.ret
            (.mcall
              (.fnref "com.google.gson.internal.reflect.ReflectionHelper")
              "RECORD_HELPER"
              [(.name "raw")])) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.getRecordComponentNames:java.lang.String[](java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_getRecordComponentNames_java_lang_String___java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.getRecordComponentNames:java.lang.String[](java.lang.Class)"
  , params := ["raw"]
  , body := (.ret
            (.mcall
              (.fnref "com.google.gson.internal.reflect.ReflectionHelper")
              "RECORD_HELPER"
              [(.name "raw")])) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.getAccessor:java.lang.reflect.Method(java.lang.Class,java.lang.reflect.Field)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_getAccessor_java_lang_reflect_Method_java_lang_Class_java_lang_refle : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.getAccessor:java.lang.reflect.Method(java.lang.Class,java.lang.reflect.Field)"
  , params := ["raw", "field"]
  , body := (.ret
            (.mcall
              (.fnref "com.google.gson.internal.reflect.ReflectionHelper")
              "RECORD_HELPER"
              [(.name "raw"), (.name "field")])) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.getCanonicalRecordConstructor:java.lang.reflect.Constructor(java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_getCanonicalRecordConstructor_java_lang_reflect_Constructor_java_lan : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.getCanonicalRecordConstructor:java.lang.reflect.Constructor(java.lang.Class)"
  , params := ["raw"]
  , body := (.ret
            (.mcall
              (.fnref "com.google.gson.internal.reflect.ReflectionHelper")
              "RECORD_HELPER"
              [(.name "raw")])) }

/-- `com.google.gson.internal.reflect.ReflectionHelper.createExceptionForUnexpectedIllegalAccess:java.lang.RuntimeException(java.lang.IllegalAccessException)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_createExceptionForUnexpectedIllegalAccess_java_lang_RuntimeException : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.createExceptionForUnexpectedIllegalAccess:java.lang.RuntimeException(java.lang.IllegalAccessException)"
  , params := ["exception"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.reflect.ReflectionHelper.createExceptionForRecordReflectionException:java.lang.RuntimeException(java.lang.ReflectiveOperationException)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_createExceptionForRecordReflectionException_java_lang_RuntimeExcepti : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper.createExceptionForRecordReflectionException:java.lang.RuntimeException(java.lang.ReflectiveOperationException)"
  , params := ["exception"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordHelper.isRecord:boolean(java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordHelper_isRecord_boolean_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordHelper.isRecord:boolean(java.lang.Class)"
  , params := ["this", "clazz"]
  , body := .skip }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordHelper.getRecordComponentNames:java.lang.String[](java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordHelper_getRecordComponentNames_java_lang_String___java_lang_Cl : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordHelper.getRecordComponentNames:java.lang.String[](java.lang.Class)"
  , params := ["this", "clazz"]
  , body := .skip }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordHelper.getCanonicalRecordConstructor:java.lang.reflect.Constructor(java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordHelper_getCanonicalRecordConstructor_java_lang_reflect_Constru : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordHelper.getCanonicalRecordConstructor:java.lang.reflect.Constructor(java.lang.Class)"
  , params := ["this", "raw"]
  , body := .skip }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordHelper.getAccessor:java.lang.reflect.Method(java.lang.Class,java.lang.reflect.Field)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordHelper_getAccessor_java_lang_reflect_Method_java_lang_Class_ja : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordHelper.getAccessor:java.lang.reflect.Method(java.lang.Class,java.lang.reflect.Field)"
  , params := ["this", "raw", "field"]
  , body := .skip }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordHelper.<init>:void()`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordHelper__init__void__ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordHelper.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordSupportedHelper.<init>:void()`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordSupportedHelper__init__void__ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordSupportedHelper.<init>:void()"
  , params := ["this"]
  , body := (.seq
            (.setField
              (.name "this")
              "isRecord"
              (.mcall
                (.name "Class")
                "class"
                [(.lit (.str "isRecord")), (.hole "op:arrayInitializer")]))
            (.seq
              (.setField
                (.name "this")
                "getRecordComponents"
                (.mcall
                  (.name "Class")
                  "class"
                  [(.lit (.str "getRecordComponents")), (.hole "op:arrayInitializer")]))
              (.seq
                .skip
                (.seq
                  (.assign
                    "classRecordComponent"
                    (.call "forName" [(.lit (.str "java.lang.reflect.RecordComponent"))]))
                  (.seq
                    (.setField
                      (.name "this")
                      "getName"
                      (.call "getMethod" [(.lit (.str "getName")), (.hole "op:arrayInitializer")]))
                    (.setField
                      (.name "this")
                      "getType"
                      (.call "getMethod" [(.lit (.str "getType")), (.hole "op:arrayInitializer")]))))))) }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordSupportedHelper.isRecord:boolean(java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordSupportedHelper_isRecord_boolean_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordSupportedHelper.isRecord:boolean(java.lang.Class)"
  , params := ["this", "raw"]
  , body := (.tryCatch (.ret (.hole "op:cast")) "__exc" (.hole "control:THROW")) }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordSupportedHelper.getRecordComponentNames:java.lang.String[](java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordSupportedHelper_getRecordComponentNames_java_lang_String___jav : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordSupportedHelper.getRecordComponentNames:java.lang.String[](java.lang.Class)"
  , params := ["this", "raw"]
  , body := (.tryCatch
            (.seq
              .skip
              (.seq
                (.assign "recordComponents" (.hole "op:cast"))
                (.seq
                  .skip
                  (.seq
                    (.assign "componentNames" (.hole "op:alloc"))
                    (.seq (.hole "control:FOR") (.ret (.name "componentNames")))))))
            "__exc"
            (.hole "control:THROW")) }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordSupportedHelper.getCanonicalRecordConstructor:java.lang.reflect.Constructor(java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordSupportedHelper_getCanonicalRecordConstructor_java_lang_reflec : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordSupportedHelper.getCanonicalRecordConstructor:java.lang.reflect.Constructor(java.lang.Class)"
  , params := ["this", "raw"]
  , body := (.tryCatch
            (.seq
              .skip
              (.seq
                (.assign "recordComponents" (.hole "op:cast"))
                (.seq
                  .skip
                  (.seq
                    (.assign "recordComponentTypes" (.hole "op:alloc"))
                    (.seq
                      (.hole "control:FOR")
                      (.ret (.call "getDeclaredConstructor" [(.hole "op:arrayInitializer")])))))))
            "__exc"
            (.hole "control:THROW")) }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordSupportedHelper.getAccessor:java.lang.reflect.Method(java.lang.Class,java.lang.reflect.Field)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordSupportedHelper_getAccessor_java_lang_reflect_Method_java_lang : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordSupportedHelper.getAccessor:java.lang.reflect.Method(java.lang.Class,java.lang.reflect.Field)"
  , params := ["this", "raw", "field"]
  , body := (.tryCatch
            (.ret (.call "getMethod" [(.call "getName" []), (.hole "op:arrayInitializer")]))
            "__exc"
            (.hole "control:THROW")) }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordNotSupportedHelper.isRecord:boolean(java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordNotSupportedHelper_isRecord_boolean_java_lang_Class_ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordNotSupportedHelper.isRecord:boolean(java.lang.Class)"
  , params := ["this", "clazz"]
  , body := (.ret (.lit (.bool false))) }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordNotSupportedHelper.getRecordComponentNames:java.lang.String[](java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordNotSupportedHelper_getRecordComponentNames_java_lang_String___ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordNotSupportedHelper.getRecordComponentNames:java.lang.String[](java.lang.Class)"
  , params := ["this", "clazz"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordNotSupportedHelper.getCanonicalRecordConstructor:java.lang.reflect.Constructor(java.lang.Class)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordNotSupportedHelper_getCanonicalRecordConstructor_java_lang_ref : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordNotSupportedHelper.getCanonicalRecordConstructor:java.lang.reflect.Constructor(java.lang.Class)"
  , params := ["this", "raw"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordNotSupportedHelper.getAccessor:java.lang.reflect.Method(java.lang.Class,java.lang.reflect.Field)`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordNotSupportedHelper_getAccessor_java_lang_reflect_Method_java_l : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordNotSupportedHelper.getAccessor:java.lang.reflect.Method(java.lang.Class,java.lang.reflect.Field)"
  , params := ["this", "raw", "field"]
  , body := (.hole "control:THROW") }

/-- `com.google.gson.internal.reflect.ReflectionHelper$RecordNotSupportedHelper.<init>:void()`  (from `internal/reflect/ReflectionHelper.java`) -/
def f_com_google_gson_internal_reflect_ReflectionHelper_RecordNotSupportedHelper__init__void__ : Func :=
  { name := "com.google.gson.internal.reflect.ReflectionHelper$RecordNotSupportedHelper.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.sql.SqlDateTypeAdapter.<init>:void()`  (from `internal/sql/SqlDateTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlDateTypeAdapter__init__void__ : Func :=
  { name := "com.google.gson.internal.sql.SqlDateTypeAdapter.<init>:void()"
  , params := ["this"]
  , body := (.seq
            (.setField (.name "this") "format" (.hole "op:alloc"))
            (.expr (.mcall (.name "this") "format" [(.lit (.str "MMM d, yyyy"))]))) }

/-- `com.google.gson.internal.sql.SqlDateTypeAdapter.read:java.sql.Date(com.google.gson.stream.JsonReader)`  (from `internal/sql/SqlDateTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlDateTypeAdapter_read_java_sql_Date_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.sql.SqlDateTypeAdapter.read:java.sql.Date(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "s" (.call "nextString" []))
                (.seq
                  (.hole "stmt:MODIFIER")
                  (.seq
                    (.expr (.name "this"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "originalTimeZone" (.mcall (.name "this") "format" []))
                        (.tryFinally
                          (.tryCatch
                            (.seq
                              .skip
                              (.seq
                                (.assign "utilDate" (.mcall (.name "this") "format" [(.name "s")]))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "$obj1" (.hole "op:alloc"))
                                    (.seq
                                      (.expr (.call "<init>" [(.call "getTime" [])]))
                                      (.ret (.name "$obj1")))))))
                            "__exc"
                            (.hole "control:THROW"))
                          (.expr (.mcall (.name "this") "format" [(.name "originalTimeZone")])))))))))) }

/-- `com.google.gson.internal.sql.SqlDateTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.sql.Date)`  (from `internal/sql/SqlDateTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlDateTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_sql_Date_ : Func :=
  { name := "com.google.gson.internal.sql.SqlDateTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.sql.Date)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "value") (.lit .unit))
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.seq
                  (.hole "stmt:MODIFIER")
                  (.seq
                    (.expr (.name "this"))
                    (.assign "dateString" (.mcall (.name "this") "format" [(.name "value")]))))
                (.expr (.call "value" [(.name "dateString")]))))) }

/-- `com.google.gson.internal.sql.SqlDateTypeAdapter.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_sql_SqlDateTypeAdapter__clinit__void__ : Func :=
  { name := "com.google.gson.internal.sql.SqlDateTypeAdapter.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.sql.SqlDateTypeAdapter")
              "FACTORY"
              (.hole "op:alloc"))
            (.expr (.mcall (.fnref "com.google.gson.internal.sql.SqlDateTypeAdapter") "FACTORY" []))) }

/-- `com.google.gson.internal.sql.SqlDateTypeAdapter.FACTORY.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/sql/SqlDateTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlDateTypeAdapter_FACTORY_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_go : Func :=
  { name := "com.google.gson.internal.sql.SqlDateTypeAdapter.FACTORY.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.ret
            (.cond
              (.binop "==" (.call "getRawType" []) (.field (.name "java.sql.Date") "class"))
              (.hole "op:cast")
              (.lit .unit))) }

/-- `com.google.gson.internal.sql.SqlDateTypeAdapter.FACTORY.TypeAdapterFactory$0.<init>:void()`  (from `internal/sql/SqlDateTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlDateTypeAdapter_FACTORY_TypeAdapterFactory_0__init__void__ : Func :=
  { name := "com.google.gson.internal.sql.SqlDateTypeAdapter.FACTORY.TypeAdapterFactory$0.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.sql.SqlTimeTypeAdapter.<init>:void()`  (from `internal/sql/SqlTimeTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlTimeTypeAdapter__init__void__ : Func :=
  { name := "com.google.gson.internal.sql.SqlTimeTypeAdapter.<init>:void()"
  , params := ["this"]
  , body := (.seq
            (.setField (.name "this") "format" (.hole "op:alloc"))
            (.expr (.mcall (.name "this") "format" [(.lit (.str "hh:mm:ss a"))]))) }

/-- `com.google.gson.internal.sql.SqlTimeTypeAdapter.read:java.sql.Time(com.google.gson.stream.JsonReader)`  (from `internal/sql/SqlTimeTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlTimeTypeAdapter_read_java_sql_Time_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.sql.SqlTimeTypeAdapter.read:java.sql.Time(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            (.ifte
              (.binop "==" (.call "peek" []) (.field (.name "JsonToken") "NULL"))
              (.seq (.expr (.call "nextNull" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.assign "s" (.call "nextString" []))
                (.seq
                  (.hole "stmt:MODIFIER")
                  (.seq
                    (.expr (.name "this"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "originalTimeZone" (.mcall (.name "this") "format" []))
                        (.tryFinally
                          (.tryCatch
                            (.seq
                              .skip
                              (.seq
                                (.assign "date" (.mcall (.name "this") "format" [(.name "s")]))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "$obj1" (.hole "op:alloc"))
                                    (.seq
                                      (.expr (.call "<init>" [(.call "getTime" [])]))
                                      (.ret (.name "$obj1")))))))
                            "__exc"
                            (.hole "control:THROW"))
                          (.expr (.mcall (.name "this") "format" [(.name "originalTimeZone")])))))))))) }

/-- `com.google.gson.internal.sql.SqlTimeTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.sql.Time)`  (from `internal/sql/SqlTimeTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlTimeTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_sql_Time_ : Func :=
  { name := "com.google.gson.internal.sql.SqlTimeTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.sql.Time)"
  , params := ["this", "out", "value"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "value") (.lit .unit))
              (.seq (.expr (.call "nullValue" [])) (.ret (.lit .unit)))
              .skip)
            (.seq
              .skip
              (.seq
                (.seq
                  (.hole "stmt:MODIFIER")
                  (.seq
                    (.expr (.name "this"))
                    (.assign "timeString" (.mcall (.name "this") "format" [(.name "value")]))))
                (.expr (.call "value" [(.name "timeString")]))))) }

/-- `com.google.gson.internal.sql.SqlTimeTypeAdapter.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_sql_SqlTimeTypeAdapter__clinit__void__ : Func :=
  { name := "com.google.gson.internal.sql.SqlTimeTypeAdapter.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.sql.SqlTimeTypeAdapter")
              "FACTORY"
              (.hole "op:alloc"))
            (.expr (.mcall (.fnref "com.google.gson.internal.sql.SqlTimeTypeAdapter") "FACTORY" []))) }

/-- `com.google.gson.internal.sql.SqlTimeTypeAdapter.FACTORY.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/sql/SqlTimeTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlTimeTypeAdapter_FACTORY_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_go : Func :=
  { name := "com.google.gson.internal.sql.SqlTimeTypeAdapter.FACTORY.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.ret
            (.cond
              (.binop "==" (.call "getRawType" []) (.field (.name "Time") "class"))
              (.hole "op:cast")
              (.lit .unit))) }

/-- `com.google.gson.internal.sql.SqlTimeTypeAdapter.FACTORY.TypeAdapterFactory$0.<init>:void()`  (from `internal/sql/SqlTimeTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlTimeTypeAdapter_FACTORY_TypeAdapterFactory_0__init__void__ : Func :=
  { name := "com.google.gson.internal.sql.SqlTimeTypeAdapter.FACTORY.TypeAdapterFactory$0.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.sql.SqlTimestampTypeAdapter.<init>:void(com.google.gson.TypeAdapter)`  (from `internal/sql/SqlTimestampTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlTimestampTypeAdapter__init__void_com_google_gson_TypeAdapter_ : Func :=
  { name := "com.google.gson.internal.sql.SqlTimestampTypeAdapter.<init>:void(com.google.gson.TypeAdapter)"
  , params := ["this", "dateTypeAdapter"]
  , body := (.setField (.name "this") "dateTypeAdapter" (.name "dateTypeAdapter")) }

/-- `com.google.gson.internal.sql.SqlTimestampTypeAdapter.read:java.sql.Timestamp(com.google.gson.stream.JsonReader)`  (from `internal/sql/SqlTimestampTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlTimestampTypeAdapter_read_java_sql_Timestamp_com_google_gson_stream_JsonReader_ : Func :=
  { name := "com.google.gson.internal.sql.SqlTimestampTypeAdapter.read:java.sql.Timestamp(com.google.gson.stream.JsonReader)"
  , params := ["this", "in"]
  , body := (.seq
            .skip
            (.seq
              (.assign "date" (.mcall (.name "this") "dateTypeAdapter" [(.name "in")]))
              (.ret
                (.cond
                  (.binop "!=" (.name "date") (.lit .unit))
                  (.hole "expr:BLOCK-impure")
                  (.lit .unit))))) }

/-- `com.google.gson.internal.sql.SqlTimestampTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.sql.Timestamp)`  (from `internal/sql/SqlTimestampTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlTimestampTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_sql_Timestamp_ : Func :=
  { name := "com.google.gson.internal.sql.SqlTimestampTypeAdapter.write:void(com.google.gson.stream.JsonWriter,java.sql.Timestamp)"
  , params := ["this", "out", "value"]
  , body := (.expr (.mcall (.name "this") "dateTypeAdapter" [(.name "out"), (.name "value")])) }

/-- `com.google.gson.internal.sql.SqlTimestampTypeAdapter.<clinit>:void()`  (from `<empty>`) -/
def f_com_google_gson_internal_sql_SqlTimestampTypeAdapter__clinit__void__ : Func :=
  { name := "com.google.gson.internal.sql.SqlTimestampTypeAdapter.<clinit>:void()"
  , params := []
  , body := (.seq
            (.setField
              (.fnref "com.google.gson.internal.sql.SqlTimestampTypeAdapter")
              "FACTORY"
              (.hole "op:alloc"))
            (.expr
              (.mcall (.fnref "com.google.gson.internal.sql.SqlTimestampTypeAdapter") "FACTORY" []))) }

/-- `com.google.gson.internal.sql.SqlTimestampTypeAdapter.FACTORY.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)`  (from `internal/sql/SqlTimestampTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlTimestampTypeAdapter_FACTORY_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_c : Func :=
  { name := "com.google.gson.internal.sql.SqlTimestampTypeAdapter.FACTORY.TypeAdapterFactory$0.create:com.google.gson.TypeAdapter(com.google.gson.Gson,com.google.gson.reflect.TypeToken)"
  , params := ["this", "gson", "typeToken"]
  , body := (.ifte
            (.binop "==" (.call "getRawType" []) (.field (.name "Timestamp") "class"))
            (.seq
              .skip
              (.seq
                (.assign "dateTypeAdapter" (.call "getAdapter" [(.field (.name "Date") "class")]))
                (.ret (.hole "op:cast"))))
            (.ret (.lit .unit))) }

/-- `com.google.gson.internal.sql.SqlTimestampTypeAdapter.FACTORY.TypeAdapterFactory$0.<init>:void()`  (from `internal/sql/SqlTimestampTypeAdapter.java`) -/
def f_com_google_gson_internal_sql_SqlTimestampTypeAdapter_FACTORY_TypeAdapterFactory_0__init__void__ : Func :=
  { name := "com.google.gson.internal.sql.SqlTimestampTypeAdapter.FACTORY.TypeAdapterFactory$0.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- `com.google.gson.internal.sql.SqlTypesSupport.<init>:void()`  (from `internal/sql/SqlTypesSupport.java`) -/
def f_com_google_gson_internal_sql_SqlTypesSupport__init__void__ : Func :=
  { name := "com.google.gson.internal.sql.SqlTypesSupport.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_com_google_gson_internal_ConstructorConstructor__init__void_java_util_Map_boolean_java_util_List_,
  f_com_google_gson_internal_ConstructorConstructor_checkInstantiable_java_lang_String_java_lang_Class_,
  f_com_google_gson_internal_ConstructorConstructor_get_com_google_gson_internal_ObjectConstructor_com_google_gson_reflect,
  f_com_google_gson_internal_ConstructorConstructor_get_com_google_gson_internal_ObjectConstructor_com_google_gson_reflect',
  f_com_google_gson_internal_ConstructorConstructor_newSpecialCollectionConstructor_com_google_gson_internal_ObjectConstru,
  f_com_google_gson_internal_ConstructorConstructor_newDefaultConstructor_com_google_gson_internal_ObjectConstructor_java_,
  f_com_google_gson_internal_ConstructorConstructor_newDefaultImplementationConstructor_com_google_gson_internal_ObjectCon,
  f_com_google_gson_internal_ConstructorConstructor_newCollectionConstructor_com_google_gson_internal_ObjectConstructor_ja,
  f_com_google_gson_internal_ConstructorConstructor_newMapConstructor_com_google_gson_internal_ObjectConstructor_java_lang,
  f_com_google_gson_internal_ConstructorConstructor_newUnsafeAllocator_com_google_gson_internal_ObjectConstructor_java_lan,
  f_com_google_gson_internal_ConstructorConstructor_toString_java_lang_String__,
  f_com_google_gson_internal_ConstructorConstructor_ThrowingObjectConstructor__init__void_java_lang_String_,
  f_com_google_gson_internal_ConstructorConstructor_ThrowingObjectConstructor_construct_java_lang_Object__,
  f_com_google_gson_internal_ConstructorConstructor_InstanceCreatorConstructor__init__void_com_google_gson_InstanceCreator,
  f_com_google_gson_internal_ConstructorConstructor_InstanceCreatorConstructor_construct_java_lang_Object__,
  f_com_google_gson_internal_ConstructorConstructor__lambda_0_java_lang_Object__,
  f_com_google_gson_internal_ConstructorConstructor__lambda_1_java_lang_Object__,
  f_com_google_gson_internal_ConstructorConstructor__lambda_2_java_lang_Object__,
  f_com_google_gson_internal_ConstructorConstructor__lambda_3_java_lang_Object__,
  f_com_google_gson_internal_Excluder_clone_com_google_gson_internal_Excluder__,
  f_com_google_gson_internal_Excluder_withVersion_com_google_gson_internal_Excluder_double_,
  f_com_google_gson_internal_Excluder_withModifiers_com_google_gson_internal_Excluder_int___,
  f_com_google_gson_internal_Excluder_disableInnerClassSerialization_com_google_gson_internal_Excluder__,
  f_com_google_gson_internal_Excluder_excludeFieldsWithoutExposeAnnotation_com_google_gson_internal_Excluder__,
  f_com_google_gson_internal_Excluder_withExclusionStrategy_com_google_gson_internal_Excluder_com_google_gson_ExclusionStr,
  f_com_google_gson_internal_Excluder_create_com_google_gson_TypeAdapter_com_google_gson_Gson_com_google_gson_reflect_Type,
  f_com_google_gson_internal_Excluder_excludeField_boolean_java_lang_reflect_Field_boolean_,
  f_com_google_gson_internal_Excluder_isExcludedByModifier_boolean_java_lang_reflect_Field_,
  f_com_google_gson_internal_Excluder_isExcludedByVersion_boolean_java_lang_reflect_Field_,
  f_com_google_gson_internal_Excluder_isExcludedByExposeAnnotation_boolean_java_lang_reflect_Field_boolean_,
  f_com_google_gson_internal_Excluder_isExcludedByStrategy_boolean_java_lang_reflect_Field_boolean_,
  f_com_google_gson_internal_Excluder_excludeClass_boolean_java_lang_Class_boolean_,
  f_com_google_gson_internal_Excluder_isInnerClass_boolean_java_lang_Class_,
  f_com_google_gson_internal_Excluder_isValidVersion_boolean_com_google_gson_annotations_Since_com_google_gson_annotations,
  f_com_google_gson_internal_Excluder_isValidSince_boolean_com_google_gson_annotations_Since_,
  f_com_google_gson_internal_Excluder_isValidUntil_boolean_com_google_gson_annotations_Until_,
  f_com_google_gson_internal_Excluder__init__void__,
  f_com_google_gson_internal_Excluder__clinit__void__,
  f_com_google_gson_internal_Excluder_create_TypeAdapter_0_read_java_lang_Object_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_Excluder_create_TypeAdapter_0_write_void_com_google_gson_stream_JsonWriter_java_lang_Object_,
  f_com_google_gson_internal_Excluder_create_TypeAdapter_0_delegate_com_google_gson_TypeAdapter__,
  f_com_google_gson_internal_Excluder_create_TypeAdapter_0__init__void__,
  f_com_google_gson_internal_GsonTypes__init__void__,
  f_com_google_gson_internal_GsonTypes_newParameterizedTypeWithOwner_java_lang_reflect_ParameterizedType_java_lang_reflect,
  f_com_google_gson_internal_GsonTypes_arrayOf_java_lang_reflect_GenericArrayType_java_lang_reflect_Type_,
  f_com_google_gson_internal_GsonTypes_subtypeOf_java_lang_reflect_WildcardType_java_lang_reflect_Type_,
  f_com_google_gson_internal_GsonTypes_supertypeOf_java_lang_reflect_WildcardType_java_lang_reflect_Type_,
  f_com_google_gson_internal_GsonTypes_canonicalize_java_lang_reflect_Type_java_lang_reflect_Type_,
  f_com_google_gson_internal_GsonTypes_getRawType_java_lang_Class_java_lang_reflect_Type_,
  f_com_google_gson_internal_GsonTypes_equal_boolean_java_lang_Object_java_lang_Object_,
  f_com_google_gson_internal_GsonTypes_equals_boolean_java_lang_reflect_Type_java_lang_reflect_Type_,
  f_com_google_gson_internal_GsonTypes_typeToString_java_lang_String_java_lang_reflect_Type_,
  f_com_google_gson_internal_GsonTypes_getGenericSupertype_java_lang_reflect_Type_java_lang_reflect_Type_java_lang_Class_j,
  f_com_google_gson_internal_GsonTypes_getSupertype_java_lang_reflect_Type_java_lang_reflect_Type_java_lang_Class_java_lan,
  f_com_google_gson_internal_GsonTypes_getArrayComponentType_java_lang_reflect_Type_java_lang_reflect_Type_,
  f_com_google_gson_internal_GsonTypes_getCollectionElementType_java_lang_reflect_Type_java_lang_reflect_Type_java_lang_Cl,
  f_com_google_gson_internal_GsonTypes_getMapKeyAndValueTypes_java_lang_reflect_Type___java_lang_reflect_Type_java_lang_Cl,
  f_com_google_gson_internal_GsonTypes_resolve_java_lang_reflect_Type_java_lang_reflect_Type_java_lang_Class_java_lang_ref,
  f_com_google_gson_internal_GsonTypes_resolve_java_lang_reflect_Type_java_lang_reflect_Type_java_lang_Class_java_lang_ref',
  f_com_google_gson_internal_GsonTypes_resolveTypeVariable_java_lang_reflect_Type_java_lang_reflect_Type_java_lang_Class_j,
  f_com_google_gson_internal_GsonTypes_indexOf_int_java_lang_Object___java_lang_Object_,
  f_com_google_gson_internal_GsonTypes_declaringClassOf_java_lang_Class_java_lang_reflect_TypeVariable_,
  f_com_google_gson_internal_GsonTypes_checkNotPrimitive_void_java_lang_reflect_Type_,
  f_com_google_gson_internal_GsonTypes_requiresOwnerType_boolean_java_lang_reflect_Type_,
  f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl__init__void_java_lang_reflect_Type_java_lang_Class_java_lang_,
  f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_getActualTypeArguments_java_lang_reflect_Type____,
  f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_getRawType_java_lang_reflect_Type__,
  f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_getOwnerType_java_lang_reflect_Type__,
  f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_equals_boolean_java_lang_Object_,
  f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_hashCodeOrZero_int_java_lang_Object_,
  f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_hashCode_int__,
  f_com_google_gson_internal_GsonTypes_ParameterizedTypeImpl_toString_java_lang_String__,
  f_com_google_gson_internal_GsonTypes_GenericArrayTypeImpl__init__void_java_lang_reflect_Type_,
  f_com_google_gson_internal_GsonTypes_GenericArrayTypeImpl_getGenericComponentType_java_lang_reflect_Type__,
  f_com_google_gson_internal_GsonTypes_GenericArrayTypeImpl_equals_boolean_java_lang_Object_,
  f_com_google_gson_internal_GsonTypes_GenericArrayTypeImpl_hashCode_int__,
  f_com_google_gson_internal_GsonTypes_GenericArrayTypeImpl_toString_java_lang_String__,
  f_com_google_gson_internal_GsonTypes_WildcardTypeImpl__init__void_java_lang_reflect_Type___java_lang_reflect_Type___,
  f_com_google_gson_internal_GsonTypes_WildcardTypeImpl_getUpperBounds_java_lang_reflect_Type____,
  f_com_google_gson_internal_GsonTypes_WildcardTypeImpl_getLowerBounds_java_lang_reflect_Type____,
  f_com_google_gson_internal_GsonTypes_WildcardTypeImpl_equals_boolean_java_lang_Object_,
  f_com_google_gson_internal_GsonTypes_WildcardTypeImpl_hashCode_int__,
  f_com_google_gson_internal_GsonTypes_WildcardTypeImpl_toString_java_lang_String__,
  f_com_google_gson_internal_GsonTypes__clinit__void__,
  f_com_google_gson_internal_JavaVersion_determineMajorJavaVersion_int__,
  f_com_google_gson_internal_JavaVersion_parseMajorJavaVersion_int_java_lang_String_,
  f_com_google_gson_internal_JavaVersion_parseDotted_int_java_lang_String_,
  f_com_google_gson_internal_JavaVersion_extractBeginningInt_int_java_lang_String_,
  f_com_google_gson_internal_JavaVersion_getMajorJavaVersion_int__,
  f_com_google_gson_internal_JavaVersion_isJava9OrLater_boolean__,
  f_com_google_gson_internal_JavaVersion__init__void__,
  f_com_google_gson_internal_JavaVersion__clinit__void__,
  f_com_google_gson_internal_JsonReaderInternalAccess_promoteNameToValue_void_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_JsonReaderInternalAccess__init__void__,
  f_com_google_gson_internal_LazilyParsedNumber__init__void_java_lang_String_,
  f_com_google_gson_internal_LazilyParsedNumber_asBigDecimal_java_math_BigDecimal__,
  f_com_google_gson_internal_LazilyParsedNumber_intValue_int__,
  f_com_google_gson_internal_LazilyParsedNumber_longValue_long__,
  f_com_google_gson_internal_LazilyParsedNumber_floatValue_float__,
  f_com_google_gson_internal_LazilyParsedNumber_doubleValue_double__,
  f_com_google_gson_internal_LazilyParsedNumber_toString_java_lang_String__,
  f_com_google_gson_internal_LazilyParsedNumber_writeReplace_java_lang_Object__,
  f_com_google_gson_internal_LazilyParsedNumber_readObject_void_java_io_ObjectInputStream_,
  f_com_google_gson_internal_LazilyParsedNumber_compareTo_int_com_google_gson_internal_LazilyParsedNumber_,
  f_com_google_gson_internal_LazilyParsedNumber_hashCode_int__,
  f_com_google_gson_internal_LazilyParsedNumber_equals_boolean_java_lang_Object_,
  f_com_google_gson_internal_LinkedTreeMap__init__void__,
  f_com_google_gson_internal_LinkedTreeMap__init__void_boolean_,
  f_com_google_gson_internal_LinkedTreeMap__init__void_java_util_Comparator_boolean_,
  f_com_google_gson_internal_LinkedTreeMap_size_int__,
  f_com_google_gson_internal_LinkedTreeMap_get_java_lang_Object_java_lang_Object_,
  f_com_google_gson_internal_LinkedTreeMap_containsKey_boolean_java_lang_Object_,
  f_com_google_gson_internal_LinkedTreeMap_put_java_lang_Object_java_lang_Object_java_lang_Object_,
  f_com_google_gson_internal_LinkedTreeMap_clear_void__,
  f_com_google_gson_internal_LinkedTreeMap_remove_java_lang_Object_java_lang_Object_,
  f_com_google_gson_internal_LinkedTreeMap_find_com_google_gson_internal_LinkedTreeMap_Node_java_lang_Object_boolean_,
  f_com_google_gson_internal_LinkedTreeMap_findByObject_com_google_gson_internal_LinkedTreeMap_Node_java_lang_Object_,
  f_com_google_gson_internal_LinkedTreeMap_findByEntry_com_google_gson_internal_LinkedTreeMap_Node_java_util_Map_Entry_,
  f_com_google_gson_internal_LinkedTreeMap_equal_boolean_java_lang_Object_java_lang_Object_,
  f_com_google_gson_internal_LinkedTreeMap_removeInternal_void_com_google_gson_internal_LinkedTreeMap_Node_boolean_,
  f_com_google_gson_internal_LinkedTreeMap_removeInternalByKey_com_google_gson_internal_LinkedTreeMap_Node_java_lang_Objec,
  f_com_google_gson_internal_LinkedTreeMap_replaceInParent_void_com_google_gson_internal_LinkedTreeMap_Node_com_google_gso,
  f_com_google_gson_internal_LinkedTreeMap_rebalance_void_com_google_gson_internal_LinkedTreeMap_Node_boolean_,
  f_com_google_gson_internal_LinkedTreeMap_rotateLeft_void_com_google_gson_internal_LinkedTreeMap_Node_,
  f_com_google_gson_internal_LinkedTreeMap_rotateRight_void_com_google_gson_internal_LinkedTreeMap_Node_,
  f_com_google_gson_internal_LinkedTreeMap_entrySet_java_util_Set__,
  f_com_google_gson_internal_LinkedTreeMap_keySet_java_util_Set__,
  f_com_google_gson_internal_LinkedTreeMap_Node__init__void_boolean_,
  f_com_google_gson_internal_LinkedTreeMap_Node__init__void_boolean_com_google_gson_internal_LinkedTreeMap_Node_java_lang_,
  f_com_google_gson_internal_LinkedTreeMap_Node_getKey_java_lang_Object__,
  f_com_google_gson_internal_LinkedTreeMap_Node_getValue_java_lang_Object__,
  f_com_google_gson_internal_LinkedTreeMap_Node_setValue_java_lang_Object_java_lang_Object_,
  f_com_google_gson_internal_LinkedTreeMap_Node_equals_boolean_java_lang_Object_,
  f_com_google_gson_internal_LinkedTreeMap_Node_hashCode_int__,
  f_com_google_gson_internal_LinkedTreeMap_Node_toString_java_lang_String__,
  f_com_google_gson_internal_LinkedTreeMap_Node_first_com_google_gson_internal_LinkedTreeMap_Node__,
  f_com_google_gson_internal_LinkedTreeMap_Node_last_com_google_gson_internal_LinkedTreeMap_Node__,
  f_com_google_gson_internal_LinkedTreeMap_LinkedTreeMapIterator__init__void__,
  f_com_google_gson_internal_LinkedTreeMap_LinkedTreeMapIterator_hasNext_boolean__,
  f_com_google_gson_internal_LinkedTreeMap_LinkedTreeMapIterator_nextNode_com_google_gson_internal_LinkedTreeMap_Node__,
  f_com_google_gson_internal_LinkedTreeMap_LinkedTreeMapIterator_remove_void__,
  f_com_google_gson_internal_LinkedTreeMap_EntrySet_size_int__,
  f_com_google_gson_internal_LinkedTreeMap_EntrySet_iterator_java_util_Iterator__,
  f_com_google_gson_internal_LinkedTreeMap_EntrySet_contains_boolean_java_lang_Object_,
  f_com_google_gson_internal_LinkedTreeMap_EntrySet_remove_boolean_java_lang_Object_,
  f_com_google_gson_internal_LinkedTreeMap_EntrySet_clear_void__,
  f_com_google_gson_internal_LinkedTreeMap_EntrySet__init__void__,
  f_com_google_gson_internal_LinkedTreeMap_EntrySet_iterator_LinkedTreeMapIterator_0_next_java_util_Map_Entry__,
  f_com_google_gson_internal_LinkedTreeMap_EntrySet_iterator_LinkedTreeMapIterator_0__init__void__,
  f_com_google_gson_internal_LinkedTreeMap_KeySet_size_int__,
  f_com_google_gson_internal_LinkedTreeMap_KeySet_iterator_java_util_Iterator__,
  f_com_google_gson_internal_LinkedTreeMap_KeySet_contains_boolean_java_lang_Object_,
  f_com_google_gson_internal_LinkedTreeMap_KeySet_remove_boolean_java_lang_Object_,
  f_com_google_gson_internal_LinkedTreeMap_KeySet_clear_void__,
  f_com_google_gson_internal_LinkedTreeMap_KeySet__init__void__,
  f_com_google_gson_internal_LinkedTreeMap_KeySet_iterator_LinkedTreeMapIterator_0_next_java_lang_Object__,
  f_com_google_gson_internal_LinkedTreeMap_KeySet_iterator_LinkedTreeMapIterator_0__init__void__,
  f_com_google_gson_internal_LinkedTreeMap_writeReplace_java_lang_Object__,
  f_com_google_gson_internal_LinkedTreeMap_readObject_void_java_io_ObjectInputStream_,
  f_com_google_gson_internal_NonNullElementWrapperList__init__void_java_util_ArrayList_,
  f_com_google_gson_internal_NonNullElementWrapperList_get_java_lang_Object_int_,
  f_com_google_gson_internal_NonNullElementWrapperList_size_int__,
  f_com_google_gson_internal_NonNullElementWrapperList_nonNull_java_lang_Object_java_lang_Object_,
  f_com_google_gson_internal_NonNullElementWrapperList_set_java_lang_Object_int_java_lang_Object_,
  f_com_google_gson_internal_NonNullElementWrapperList_add_void_int_java_lang_Object_,
  f_com_google_gson_internal_NonNullElementWrapperList_remove_java_lang_Object_int_,
  f_com_google_gson_internal_NonNullElementWrapperList_clear_void__,
  f_com_google_gson_internal_NonNullElementWrapperList_remove_boolean_java_lang_Object_,
  f_com_google_gson_internal_NonNullElementWrapperList_removeAll_boolean_java_util_Collection_,
  f_com_google_gson_internal_NonNullElementWrapperList_retainAll_boolean_java_util_Collection_,
  f_com_google_gson_internal_NonNullElementWrapperList_contains_boolean_java_lang_Object_,
  f_com_google_gson_internal_NonNullElementWrapperList_indexOf_int_java_lang_Object_,
  f_com_google_gson_internal_NonNullElementWrapperList_lastIndexOf_int_java_lang_Object_,
  f_com_google_gson_internal_NonNullElementWrapperList_toArray_java_lang_Object____,
  f_com_google_gson_internal_NonNullElementWrapperList_toArray_java_lang_Object___java_lang_Object___,
  f_com_google_gson_internal_NonNullElementWrapperList_sort_void_java_util_Comparator_,
  f_com_google_gson_internal_NonNullElementWrapperList_spliterator_java_util_Spliterator__,
  f_com_google_gson_internal_NonNullElementWrapperList_equals_boolean_java_lang_Object_,
  f_com_google_gson_internal_NonNullElementWrapperList_hashCode_int__,
  f_com_google_gson_internal_NumberLimits__init__void__,
  f_com_google_gson_internal_NumberLimits_checkNumberStringLength_void_java_lang_String_,
  f_com_google_gson_internal_NumberLimits_parseBigDecimal_java_math_BigDecimal_java_lang_String_,
  f_com_google_gson_internal_NumberLimits_parseBigInteger_java_math_BigInteger_java_lang_String_,
  f_com_google_gson_internal_NumberLimits__clinit__void__,
  f_com_google_gson_internal_ObjectConstructor_construct_java_lang_Object__,
  f_com_google_gson_internal_PreJava9DateFormatProvider__init__void__,
  f_com_google_gson_internal_PreJava9DateFormatProvider_getUsDateTimeFormat_java_text_DateFormat_int_int_,
  f_com_google_gson_internal_PreJava9DateFormatProvider_getDatePartOfDateTimePattern_java_lang_String_int_,
  f_com_google_gson_internal_PreJava9DateFormatProvider_getTimePartOfDateTimePattern_java_lang_String_int_,
  f_com_google_gson_internal_Primitives__init__void__,
  f_com_google_gson_internal_Primitives_isPrimitive_boolean_java_lang_reflect_Type_,
  f_com_google_gson_internal_Primitives_isWrapperType_boolean_java_lang_reflect_Type_,
  f_com_google_gson_internal_Primitives_wrap_java_lang_Class_java_lang_Class_,
  f_com_google_gson_internal_Primitives_unwrap_java_lang_Class_java_lang_Class_,
  f_com_google_gson_internal_ReflectionAccessFilterHelper__init__void__,
  f_com_google_gson_internal_ReflectionAccessFilterHelper_isJavaType_boolean_java_lang_Class_,
  f_com_google_gson_internal_ReflectionAccessFilterHelper_isJavaType_boolean_java_lang_String_,
  f_com_google_gson_internal_ReflectionAccessFilterHelper_isAndroidType_boolean_java_lang_Class_,
  f_com_google_gson_internal_ReflectionAccessFilterHelper_isAndroidType_boolean_java_lang_String_,
  f_com_google_gson_internal_ReflectionAccessFilterHelper_isAnyPlatformType_boolean_java_lang_Class_,
  f_com_google_gson_internal_ReflectionAccessFilterHelper_getFilterResult_com_google_gson_ReflectionAccessFilter_FilterRes,
  f_com_google_gson_internal_ReflectionAccessFilterHelper_canAccess_boolean_java_lang_reflect_AccessibleObject_java_lang_O,
  f_com_google_gson_internal_ReflectionAccessFilterHelper_AccessChecker_canAccess_boolean_java_lang_reflect_AccessibleObje,
  f_com_google_gson_internal_ReflectionAccessFilterHelper_AccessChecker__init__void__,
  f_com_google_gson_internal_Streams__init__void__,
  f_com_google_gson_internal_Streams_parse_com_google_gson_JsonElement_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_Streams_write_void_com_google_gson_JsonElement_com_google_gson_stream_JsonWriter_,
  f_com_google_gson_internal_Streams_writerForAppendable_java_io_Writer_java_lang_Appendable_,
  f_com_google_gson_internal_Streams_AppendableWriter__init__void_java_lang_Appendable_,
  f_com_google_gson_internal_Streams_AppendableWriter_write_void_char___int_int_,
  f_com_google_gson_internal_Streams_AppendableWriter_flush_void__,
  f_com_google_gson_internal_Streams_AppendableWriter_close_void__,
  f_com_google_gson_internal_Streams_AppendableWriter_write_void_int_,
  f_com_google_gson_internal_Streams_AppendableWriter_write_void_java_lang_String_int_int_,
  f_com_google_gson_internal_Streams_AppendableWriter_append_java_io_Writer_java_lang_CharSequence_,
  f_com_google_gson_internal_Streams_AppendableWriter_append_java_io_Writer_java_lang_CharSequence_int_int_,
  f_com_google_gson_internal_Streams_AppendableWriter_CurrentWrite_setChars_void_char___,
  f_com_google_gson_internal_Streams_AppendableWriter_CurrentWrite_length_int__,
  f_com_google_gson_internal_Streams_AppendableWriter_CurrentWrite_charAt_char_int_,
  f_com_google_gson_internal_Streams_AppendableWriter_CurrentWrite_subSequence_java_lang_CharSequence_int_int_,
  f_com_google_gson_internal_Streams_AppendableWriter_CurrentWrite_toString_java_lang_String__,
  f_com_google_gson_internal_Streams_AppendableWriter_CurrentWrite__init__void__,
  f_com_google_gson_internal_TroubleshootingGuide__init__void__,
  f_com_google_gson_internal_TroubleshootingGuide_createUrl_java_lang_String_java_lang_String_,
  f_com_google_gson_internal_UnsafeAllocator_newInstance_java_lang_Object_java_lang_Class_,
  f_com_google_gson_internal_UnsafeAllocator_assertInstantiable_void_java_lang_Class_,
  f_com_google_gson_internal_UnsafeAllocator_create_com_google_gson_internal_UnsafeAllocator__,
  f_com_google_gson_internal_UnsafeAllocator__init__void__,
  f_com_google_gson_internal_UnsafeAllocator__clinit__void__,
  f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_0_newInstance_java_lang_Object_java_lang_Class_,
  f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_0__init__void__,
  f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_1_newInstance_java_lang_Object_java_lang_Class_,
  f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_1__init__void__,
  f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_2_newInstance_java_lang_Object_java_lang_Class_,
  f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_2__init__void__,
  f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_3_newInstance_java_lang_Object_java_lang_Class_,
  f_com_google_gson_internal_UnsafeAllocator_create_UnsafeAllocator_3__init__void__,
  f_com_google_gson_internal_bind_ArrayTypeAdapter__init__void_com_google_gson_Gson_com_google_gson_TypeAdapter_java_lang_,
  f_com_google_gson_internal_bind_ArrayTypeAdapter_read_java_lang_Object_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_bind_ArrayTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Object_,
  f_com_google_gson_internal_bind_ArrayTypeAdapter__clinit__void__,
  f_com_google_gson_internal_bind_ArrayTypeAdapter_FACTORY_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_goo,
  f_com_google_gson_internal_bind_ArrayTypeAdapter_FACTORY_TypeAdapterFactory_0__init__void__,
  f_com_google_gson_internal_bind_CollectionTypeAdapterFactory__init__void_com_google_gson_internal_ConstructorConstructor,
  f_com_google_gson_internal_bind_CollectionTypeAdapterFactory_create_com_google_gson_TypeAdapter_com_google_gson_Gson_com,
  f_com_google_gson_internal_bind_CollectionTypeAdapterFactory_Adapter__init__void_com_google_gson_TypeAdapter_com_google_,
  f_com_google_gson_internal_bind_CollectionTypeAdapterFactory_Adapter_read_java_util_Collection_com_google_gson_stream_Js,
  f_com_google_gson_internal_bind_CollectionTypeAdapterFactory_Adapter_write_void_com_google_gson_stream_JsonWriter_java_u,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType__init__void_java_lang_Class_,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType_deserialize_java_util_Date_java_util_Date_,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType_createFactory_com_google_gson_TypeAdapterFactory_com_goo,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType_createAdapterFactory_com_google_gson_TypeAdapterFactory_,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType_createAdapterFactory_com_google_gson_TypeAdapterFactory_',
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType__clinit__void__,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType_DATE_DateType_0_deserialize_java_util_Date_java_util_Dat,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DateType_DATE_DateType_0__init__void__,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter__init__void_com_google_gson_internal_bind_DefaultDateTypeAdapter_,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter__init__void_com_google_gson_internal_bind_DefaultDateTypeAdapter_',
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_util_Date_,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_read_java_util_Date_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_deserializeToDate_java_util_Date_com_google_gson_stream_JsonReade,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_toString_java_lang_String__,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter__clinit__void__,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DEFAULT_STYLE_FACTORY_TypeAdapterFactory_0_create_com_google_gson,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DEFAULT_STYLE_FACTORY_TypeAdapterFactory_0_toString__unresolvedSi,
  f_com_google_gson_internal_bind_DefaultDateTypeAdapter_DEFAULT_STYLE_FACTORY_TypeAdapterFactory_0__init__void__,
  f_com_google_gson_internal_bind_EnumTypeAdapter_calculateHashMapCapacity_int_int_,
  f_com_google_gson_internal_bind_EnumTypeAdapter__init__void_java_lang_Class_,
  f_com_google_gson_internal_bind_EnumTypeAdapter_read_java_lang_Enum_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_bind_EnumTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Enum_,
  f_com_google_gson_internal_bind_EnumTypeAdapter__clinit__void__,
  f_com_google_gson_internal_bind_EnumTypeAdapter_FACTORY_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_goog,
  f_com_google_gson_internal_bind_EnumTypeAdapter_FACTORY_TypeAdapterFactory_0__init__void__,
  f_com_google_gson_internal_bind_IgnoreJRERequirement__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_get_com_google_gson_TypeAdapterFactory__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_localDateTime_com_google_gson_TypeAdapter_com_google_gson_Gson_,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetDateTime_com_google_gson_TypeAdapter_com_google_gson_Gson_,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetTime_com_google_gson_TypeAdapter_com_google_gson_Gson_,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_zonedDateTime_com_google_gson_TypeAdapter_com_google_gson_Gson_,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_requireNonNullField_java_lang_Object_java_lang_Object_java_lang_Str,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters__clinit__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_DURATION_IntegerFieldsTypeAdapter_0_create_java_time_Duration_long_,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_DURATION_IntegerFieldsTypeAdapter_0_integerValues_long___java_time_,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_DURATION_IntegerFieldsTypeAdapter_0__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_INSTANT_IntegerFieldsTypeAdapter_1_create_java_time_Instant_long___,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_INSTANT_IntegerFieldsTypeAdapter_1_integerValues_long___java_time_I,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_INSTANT_IntegerFieldsTypeAdapter_1__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_LOCAL_DATE_IntegerFieldsTypeAdapter_2_create_java_time_LocalDate_lo,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_LOCAL_DATE_IntegerFieldsTypeAdapter_2_integerValues_long___java_tim,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_LOCAL_DATE_IntegerFieldsTypeAdapter_2__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_LOCAL_TIME_IntegerFieldsTypeAdapter_3_create_java_time_LocalTime_lo,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_LOCAL_TIME_IntegerFieldsTypeAdapter_3_integerValues_long___java_tim,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_LOCAL_TIME_IntegerFieldsTypeAdapter_3__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_MONTH_DAY_IntegerFieldsTypeAdapter_4_create_java_time_MonthDay_long,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_MONTH_DAY_IntegerFieldsTypeAdapter_4_integerValues_long___java_time,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_MONTH_DAY_IntegerFieldsTypeAdapter_4__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_PERIOD_IntegerFieldsTypeAdapter_5_create_java_time_Period_long___,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_PERIOD_IntegerFieldsTypeAdapter_5_integerValues_long___java_time_Pe,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_PERIOD_IntegerFieldsTypeAdapter_5__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_YEAR_IntegerFieldsTypeAdapter_6_create_java_time_Year_long___,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_YEAR_IntegerFieldsTypeAdapter_6_integerValues_long___java_time_Year,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_YEAR_IntegerFieldsTypeAdapter_6__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_YEAR_MONTH_IntegerFieldsTypeAdapter_7_create_java_time_YearMonth_lo,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_YEAR_MONTH_IntegerFieldsTypeAdapter_7_integerValues_long___java_tim,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_YEAR_MONTH_IntegerFieldsTypeAdapter_7__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_ZONE_ID_TypeAdapter_8_read_java_time_ZoneId_com_google_gson_stream_,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_ZONE_ID_TypeAdapter_8_write_void_com_google_gson_stream_JsonWriter_,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_ZONE_ID_TypeAdapter_8__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_JAVA_TIME_FACTORY_TypeAdapterFactory_9_create_com_google_gson_TypeA,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_JAVA_TIME_FACTORY_TypeAdapterFactory_9__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_localDateTime_TypeAdapter_0_read_java_time_LocalDateTime_com_google,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_localDateTime_TypeAdapter_0_write_void_com_google_gson_stream_JsonW,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_localDateTime_TypeAdapter_0__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetDateTime_TypeAdapter_0_read_java_time_OffsetDateTime_com_goog,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetDateTime_TypeAdapter_0_write_void_com_google_gson_stream_Json,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetDateTime_TypeAdapter_0__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetTime_TypeAdapter_0_read_java_time_OffsetTime_com_google_gson_,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetTime_TypeAdapter_0_write_void_com_google_gson_stream_JsonWrit,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_offsetTime_TypeAdapter_0__init__void__,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_zonedDateTime_TypeAdapter_0_read_java_time_ZonedDateTime_com_google,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_zonedDateTime_TypeAdapter_0_write_void_com_google_gson_stream_JsonW,
  f_com_google_gson_internal_bind_JavaTimeTypeAdapters_zonedDateTime_TypeAdapter_0__init__void__,
  f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_DummyTypeAdapterFactory_create_com_google_gson_T,
  f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_DummyTypeAdapterFactory__init__void__,
  f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory__init__void_com_google_gson_internal_Constructor,
  f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_getAnnotation_com_google_gson_annotations_JsonAd,
  f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_create_com_google_gson_TypeAdapter_com_google_gs,
  f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_createAdapter_java_lang_Object_com_google_gson_i,
  f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_putFactoryAndGetCurrent_com_google_gson_TypeAdap,
  f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_getTypeAdapter_com_google_gson_TypeAdapter_com_g,
  f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_areSameFactories_boolean_com_google_gson_TypeAda,
  f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory_isClassJsonAdapterFactory_boolean_com_google_gso,
  f_com_google_gson_internal_bind_JsonAdapterAnnotationTypeAdapterFactory__clinit__void__,
  f_com_google_gson_internal_bind_JsonElementTypeAdapter__init__void__,
  f_com_google_gson_internal_bind_JsonElementTypeAdapter_tryBeginNesting_com_google_gson_JsonElement_com_google_gson_strea,
  f_com_google_gson_internal_bind_JsonElementTypeAdapter_readTerminal_com_google_gson_JsonElement_com_google_gson_stream_J,
  f_com_google_gson_internal_bind_JsonElementTypeAdapter_read_com_google_gson_JsonElement_com_google_gson_stream_JsonReade,
  f_com_google_gson_internal_bind_JsonElementTypeAdapter_write_void_com_google_gson_stream_JsonWriter_com_google_gson_Json,
  f_com_google_gson_internal_bind_JsonElementTypeAdapter__clinit__void__,
  f_com_google_gson_internal_bind_JsonTreeReader__init__void_com_google_gson_JsonElement_,
  f_com_google_gson_internal_bind_JsonTreeReader_beginArray_void__,
  f_com_google_gson_internal_bind_JsonTreeReader_endArray_void__,
  f_com_google_gson_internal_bind_JsonTreeReader_beginObject_void__,
  f_com_google_gson_internal_bind_JsonTreeReader_endObject_void__,
  f_com_google_gson_internal_bind_JsonTreeReader_hasNext_boolean__,
  f_com_google_gson_internal_bind_JsonTreeReader_peek_com_google_gson_stream_JsonToken__,
  f_com_google_gson_internal_bind_JsonTreeReader_peekStack_java_lang_Object__,
  f_com_google_gson_internal_bind_JsonTreeReader_popStack_java_lang_Object__,
  f_com_google_gson_internal_bind_JsonTreeReader_expect_void_com_google_gson_stream_JsonToken_,
  f_com_google_gson_internal_bind_JsonTreeReader_nextName_java_lang_String_boolean_,
  f_com_google_gson_internal_bind_JsonTreeReader_nextName_java_lang_String__,
  f_com_google_gson_internal_bind_JsonTreeReader_nextString_java_lang_String__,
  f_com_google_gson_internal_bind_JsonTreeReader_nextBoolean_boolean__,
  f_com_google_gson_internal_bind_JsonTreeReader_nextNull_void__,
  f_com_google_gson_internal_bind_JsonTreeReader_nextDouble_double__,
  f_com_google_gson_internal_bind_JsonTreeReader_nextLong_long__,
  f_com_google_gson_internal_bind_JsonTreeReader_nextInt_int__,
  f_com_google_gson_internal_bind_JsonTreeReader_nextJsonElement_com_google_gson_JsonElement__,
  f_com_google_gson_internal_bind_JsonTreeReader_close_void__,
  f_com_google_gson_internal_bind_JsonTreeReader_skipValue_void__,
  f_com_google_gson_internal_bind_JsonTreeReader_toString_java_lang_String__,
  f_com_google_gson_internal_bind_JsonTreeReader_promoteNameToValue_void__,
  f_com_google_gson_internal_bind_JsonTreeReader_push_void_java_lang_Object_,
  f_com_google_gson_internal_bind_JsonTreeReader_getPath_java_lang_String_boolean_,
  f_com_google_gson_internal_bind_JsonTreeReader_getPath_java_lang_String__,
  f_com_google_gson_internal_bind_JsonTreeReader_getPreviousPath_java_lang_String__,
  f_com_google_gson_internal_bind_JsonTreeReader_locationString_java_lang_String__,
  f_com_google_gson_internal_bind_JsonTreeReader_isAllAscii_boolean_java_lang_String_,
  f_com_google_gson_internal_bind_JsonTreeReader_validateAscii_void_java_lang_String_,
  f_com_google_gson_internal_bind_JsonTreeReader_numberFormatException_java_lang_NumberFormatException_java_lang_String_ja,
  f_com_google_gson_internal_bind_JsonTreeReader__clinit__void__,
  f_com_google_gson_internal_bind_JsonTreeReader_UNREADABLE_READER_Reader_0_read_int_char___int_int_,
  f_com_google_gson_internal_bind_JsonTreeReader_UNREADABLE_READER_Reader_0_close_void__,
  f_com_google_gson_internal_bind_JsonTreeReader_UNREADABLE_READER_Reader_0__init__void__,
  f_com_google_gson_internal_bind_JsonTreeWriter__init__void__,
  f_com_google_gson_internal_bind_JsonTreeWriter_get_com_google_gson_JsonElement__,
  f_com_google_gson_internal_bind_JsonTreeWriter_peek_com_google_gson_JsonElement__,
  f_com_google_gson_internal_bind_JsonTreeWriter_put_void_com_google_gson_JsonElement_,
  f_com_google_gson_internal_bind_JsonTreeWriter_beginArray_com_google_gson_stream_JsonWriter__,
  f_com_google_gson_internal_bind_JsonTreeWriter_endArray_com_google_gson_stream_JsonWriter__,
  f_com_google_gson_internal_bind_JsonTreeWriter_beginObject_com_google_gson_stream_JsonWriter__,
  f_com_google_gson_internal_bind_JsonTreeWriter_endObject_com_google_gson_stream_JsonWriter__,
  f_com_google_gson_internal_bind_JsonTreeWriter_name_com_google_gson_stream_JsonWriter_java_lang_String_,
  f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_java_lang_String_,
  f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_boolean_,
  f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_java_lang_Boolean_,
  f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_float_,
  f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_double_,
  f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_long_,
  f_com_google_gson_internal_bind_JsonTreeWriter_value_com_google_gson_stream_JsonWriter_java_lang_Number_,
  f_com_google_gson_internal_bind_JsonTreeWriter_nullValue_com_google_gson_stream_JsonWriter__,
  f_com_google_gson_internal_bind_JsonTreeWriter_jsonValue_com_google_gson_stream_JsonWriter_java_lang_String_,
  f_com_google_gson_internal_bind_JsonTreeWriter_flush_void__,
  f_com_google_gson_internal_bind_JsonTreeWriter_close_void__,
  f_com_google_gson_internal_bind_JsonTreeWriter__clinit__void__,
  f_com_google_gson_internal_bind_JsonTreeWriter_UNWRITABLE_WRITER_Writer_0_write_void_char___int_int_,
  f_com_google_gson_internal_bind_JsonTreeWriter_UNWRITABLE_WRITER_Writer_0_flush_void__,
  f_com_google_gson_internal_bind_JsonTreeWriter_UNWRITABLE_WRITER_Writer_0_close_void__,
  f_com_google_gson_internal_bind_JsonTreeWriter_UNWRITABLE_WRITER_Writer_0__init__void__,
  f_com_google_gson_internal_bind_MapTypeAdapterFactory__init__void_com_google_gson_internal_ConstructorConstructor_boolea,
  f_com_google_gson_internal_bind_MapTypeAdapterFactory_create_com_google_gson_TypeAdapter_com_google_gson_Gson_com_google,
  f_com_google_gson_internal_bind_MapTypeAdapterFactory_getKeyAdapter_com_google_gson_TypeAdapter_com_google_gson_Gson_jav,
  f_com_google_gson_internal_bind_MapTypeAdapterFactory_Adapter__init__void_com_google_gson_TypeAdapter_com_google_gson_Ty,
  f_com_google_gson_internal_bind_MapTypeAdapterFactory_Adapter_read_java_util_Map_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_bind_MapTypeAdapterFactory_Adapter_write_void_com_google_gson_stream_JsonWriter_java_util_Map,
  f_com_google_gson_internal_bind_MapTypeAdapterFactory_Adapter_keyToString_java_lang_String_com_google_gson_JsonElement_,
  f_com_google_gson_internal_bind_NumberTypeAdapter__init__void_com_google_gson_ToNumberStrategy_,
  f_com_google_gson_internal_bind_NumberTypeAdapter_newFactory_com_google_gson_TypeAdapterFactory_com_google_gson_ToNumber,
  f_com_google_gson_internal_bind_NumberTypeAdapter_getFactory_com_google_gson_TypeAdapterFactory_com_google_gson_ToNumber,
  f_com_google_gson_internal_bind_NumberTypeAdapter_read_java_lang_Number_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_bind_NumberTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Number_,
  f_com_google_gson_internal_bind_NumberTypeAdapter__clinit__void__,
  f_com_google_gson_internal_bind_NumberTypeAdapter_newFactory_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com,
  f_com_google_gson_internal_bind_NumberTypeAdapter_newFactory_TypeAdapterFactory_0__init__void__,
  f_com_google_gson_internal_bind_ObjectTypeAdapter__init__void_com_google_gson_Gson_com_google_gson_ToNumberStrategy_,
  f_com_google_gson_internal_bind_ObjectTypeAdapter_newFactory_com_google_gson_TypeAdapterFactory_com_google_gson_ToNumber,
  f_com_google_gson_internal_bind_ObjectTypeAdapter_getFactory_com_google_gson_TypeAdapterFactory_com_google_gson_ToNumber,
  f_com_google_gson_internal_bind_ObjectTypeAdapter_tryBeginNesting_java_lang_Object_com_google_gson_stream_JsonReader_com,
  f_com_google_gson_internal_bind_ObjectTypeAdapter_readTerminal_java_lang_Object_com_google_gson_stream_JsonReader_com_go,
  f_com_google_gson_internal_bind_ObjectTypeAdapter_read_java_lang_Object_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_bind_ObjectTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Object_,
  f_com_google_gson_internal_bind_ObjectTypeAdapter__clinit__void__,
  f_com_google_gson_internal_bind_ObjectTypeAdapter_newFactory_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com,
  f_com_google_gson_internal_bind_ObjectTypeAdapter_newFactory_TypeAdapterFactory_0__init__void__,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory__init__void_com_google_gson_internal_ConstructorConstructor,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_includeField_boolean_java_lang_reflect_Field_boolean_,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_getFieldNames_java_util_List_java_lang_reflect_Field_,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_create_com_google_gson_TypeAdapter_com_google_gson_Gson_com,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_checkAccessible_void_java_lang_Object_java_lang_reflect_Acc,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_createBoundField_com_google_gson_internal_bind_ReflectiveTy,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_FieldsData__init__void_java_util_Map_java_util_List_,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_FieldsData__clinit__void__,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_createDuplicateFieldException_java_lang_IllegalArgumentExce,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_getBoundFields_com_google_gson_internal_bind_ReflectiveType,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_BoundField__init__void_java_lang_String_java_lang_reflect_F,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_BoundField_write_void_com_google_gson_stream_JsonWriter_jav,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_BoundField_readIntoArray_void_com_google_gson_stream_JsonRe,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_BoundField_readIntoField_void_com_google_gson_stream_JsonRe,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_Adapter__init__void_com_google_gson_internal_bind_Reflectiv,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_Adapter_write_void_com_google_gson_stream_JsonWriter_java_l,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_Adapter_read_java_lang_Object_com_google_gson_stream_JsonRe,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_Adapter_createAccumulator_java_lang_Object__,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_Adapter_readField_void_java_lang_Object_com_google_gson_str,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_Adapter_finalize_java_lang_Object_java_lang_Object_,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_FieldReflectionAdapter__init__void_com_google_gson_internal,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_FieldReflectionAdapter_createAccumulator_java_lang_Object__,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_FieldReflectionAdapter_readField_void_java_lang_Object_com_,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_FieldReflectionAdapter_finalize_java_lang_Object_java_lang_,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_RecordAdapter__init__void_java_lang_Class_com_google_gson_i,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_RecordAdapter_primitiveDefaults_java_util_Map__,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_RecordAdapter_createAccumulator_java_lang_Object____,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_RecordAdapter_readField_void_java_lang_Object___com_google_,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_RecordAdapter_finalize_java_lang_Object_java_lang_Object___,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_RecordAdapter__clinit__void__,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_create_TypeAdapter_0_read_java_lang_Object_com_google_gson_,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_create_TypeAdapter_0_write_void_com_google_gson_stream_Json,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_create_TypeAdapter_0_toString__unresolvedSignature__0_,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_create_TypeAdapter_0__init__void__,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_createBoundField_BoundField_0_write_void_com_google_gson_st,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_createBoundField_BoundField_0_readIntoArray_void_com_google,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_createBoundField_BoundField_0_readIntoField_void_com_google,
  f_com_google_gson_internal_bind_ReflectiveTypeAdapterFactory_createBoundField_BoundField_0__init__void__,
  f_com_google_gson_internal_bind_SerializationDelegatingTypeAdapter_getSerializationDelegate_com_google_gson_TypeAdapter_,
  f_com_google_gson_internal_bind_SerializationDelegatingTypeAdapter__init__void__,
  f_com_google_gson_internal_bind_TreeTypeAdapter__init__void_com_google_gson_JsonSerializer_com_google_gson_JsonDeseriali,
  f_com_google_gson_internal_bind_TreeTypeAdapter__init__void_com_google_gson_JsonSerializer_com_google_gson_JsonDeseriali',
  f_com_google_gson_internal_bind_TreeTypeAdapter_read_java_lang_Object_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_bind_TreeTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Object_,
  f_com_google_gson_internal_bind_TreeTypeAdapter_delegate_com_google_gson_TypeAdapter__,
  f_com_google_gson_internal_bind_TreeTypeAdapter_getSerializationDelegate_com_google_gson_TypeAdapter__,
  f_com_google_gson_internal_bind_TreeTypeAdapter_newFactory_com_google_gson_TypeAdapterFactory_com_google_gson_reflect_Ty,
  f_com_google_gson_internal_bind_TreeTypeAdapter_newFactoryWithMatchRawType_com_google_gson_TypeAdapterFactory_com_google,
  f_com_google_gson_internal_bind_TreeTypeAdapter_newTypeHierarchyFactory_com_google_gson_TypeAdapterFactory_java_lang_Cla,
  f_com_google_gson_internal_bind_TreeTypeAdapter_SingleTypeFactory__init__void_java_lang_Object_com_google_gson_reflect_T,
  f_com_google_gson_internal_bind_TreeTypeAdapter_SingleTypeFactory_create_com_google_gson_TypeAdapter_com_google_gson_Gso,
  f_com_google_gson_internal_bind_TreeTypeAdapter_GsonContextImpl_serialize_com_google_gson_JsonElement_java_lang_Object_,
  f_com_google_gson_internal_bind_TreeTypeAdapter_GsonContextImpl_serialize_com_google_gson_JsonElement_java_lang_Object_j,
  f_com_google_gson_internal_bind_TreeTypeAdapter_GsonContextImpl_deserialize_java_lang_Object_com_google_gson_JsonElement,
  f_com_google_gson_internal_bind_TreeTypeAdapter_GsonContextImpl__init__void__,
  f_com_google_gson_internal_bind_TypeAdapterRuntimeTypeWrapper__init__void_com_google_gson_Gson_com_google_gson_TypeAdapt,
  f_com_google_gson_internal_bind_TypeAdapterRuntimeTypeWrapper_read_java_lang_Object_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_bind_TypeAdapterRuntimeTypeWrapper_write_void_com_google_gson_stream_JsonWriter_java_lang_Obj,
  f_com_google_gson_internal_bind_TypeAdapterRuntimeTypeWrapper_isReflective_boolean_com_google_gson_TypeAdapter_,
  f_com_google_gson_internal_bind_TypeAdapterRuntimeTypeWrapper_getRuntimeTypeIfMoreSpecific_java_lang_reflect_Type_java_l,
  f_com_google_gson_internal_bind_TypeAdapters__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_atomicLongAdapter_com_google_gson_TypeAdapter_com_google_gson_TypeAdapter_,
  f_com_google_gson_internal_bind_TypeAdapters_atomicLongArrayAdapter_com_google_gson_TypeAdapter_com_google_gson_TypeAdap,
  f_com_google_gson_internal_bind_TypeAdapters_FloatAdapter__init__void_boolean_,
  f_com_google_gson_internal_bind_TypeAdapters_FloatAdapter_read_java_lang_Float_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_bind_TypeAdapters_FloatAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Number_,
  f_com_google_gson_internal_bind_TypeAdapters_DoubleAdapter__init__void_boolean_,
  f_com_google_gson_internal_bind_TypeAdapters_DoubleAdapter_read_java_lang_Double_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_bind_TypeAdapters_DoubleAdapter_write_void_com_google_gson_stream_JsonWriter_java_lang_Number,
  f_com_google_gson_internal_bind_TypeAdapters_checkValidFloatingPoint_void_double_,
  f_com_google_gson_internal_bind_TypeAdapters_IntegerFieldsTypeAdapter__init__void_java_lang_String___,
  f_com_google_gson_internal_bind_TypeAdapters_IntegerFieldsTypeAdapter_create_java_lang_Object_long___,
  f_com_google_gson_internal_bind_TypeAdapters_IntegerFieldsTypeAdapter_integerValues_long___java_lang_Object_,
  f_com_google_gson_internal_bind_TypeAdapters_IntegerFieldsTypeAdapter_read_java_lang_Object_com_google_gson_stream_JsonR,
  f_com_google_gson_internal_bind_TypeAdapters_IntegerFieldsTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_,
  f_com_google_gson_internal_bind_TypeAdapters_FactorySupplier_get_com_google_gson_TypeAdapterFactory__,
  f_com_google_gson_internal_bind_TypeAdapters_javaTimeTypeAdapterFactory_com_google_gson_TypeAdapterFactory__,
  f_com_google_gson_internal_bind_TypeAdapters_newFactory_com_google_gson_TypeAdapterFactory_com_google_gson_reflect_TypeT,
  f_com_google_gson_internal_bind_TypeAdapters_newFactory_com_google_gson_TypeAdapterFactory_java_lang_Class_com_google_gs,
  f_com_google_gson_internal_bind_TypeAdapters_newFactory_com_google_gson_TypeAdapterFactory_java_lang_Class_java_lang_Cla,
  f_com_google_gson_internal_bind_TypeAdapters_newFactoryForMultipleTypes_com_google_gson_TypeAdapterFactory_java_lang_Cla,
  f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_com_google_gson_TypeAdapterFactory_java_lang_Class_,
  f_com_google_gson_internal_bind_TypeAdapters__clinit__void__,
  f_com_google_gson_internal_bind_TypeAdapters_CLASS_TypeAdapter_0_write__unresolvedSignature__2_,
  f_com_google_gson_internal_bind_TypeAdapters_CLASS_TypeAdapter_0_read__unresolvedSignature__1_,
  f_com_google_gson_internal_bind_TypeAdapters_CLASS_TypeAdapter_0__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_BIT_SET_TypeAdapter_1_read_java_util_BitSet_com_google_gson_stream_JsonRead,
  f_com_google_gson_internal_bind_TypeAdapters_BIT_SET_TypeAdapter_1_write_void_com_google_gson_stream_JsonWriter_java_uti,
  f_com_google_gson_internal_bind_TypeAdapters_BIT_SET_TypeAdapter_1__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_BOOLEAN_TypeAdapter_2_read__unresolvedSignature__1_,
  f_com_google_gson_internal_bind_TypeAdapters_BOOLEAN_TypeAdapter_2_write__unresolvedSignature__2_,
  f_com_google_gson_internal_bind_TypeAdapters_BOOLEAN_TypeAdapter_2__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_BOOLEAN_AS_STRING_TypeAdapter_3_read__unresolvedSignature__1_,
  f_com_google_gson_internal_bind_TypeAdapters_BOOLEAN_AS_STRING_TypeAdapter_3_write__unresolvedSignature__2_,
  f_com_google_gson_internal_bind_TypeAdapters_BOOLEAN_AS_STRING_TypeAdapter_3__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_BYTE_TypeAdapter_4_read__unresolvedSignature__1_,
  f_com_google_gson_internal_bind_TypeAdapters_BYTE_TypeAdapter_4_write__unresolvedSignature__2_,
  f_com_google_gson_internal_bind_TypeAdapters_BYTE_TypeAdapter_4__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_SHORT_TypeAdapter_5_read__unresolvedSignature__1_,
  f_com_google_gson_internal_bind_TypeAdapters_SHORT_TypeAdapter_5_write__unresolvedSignature__2_,
  f_com_google_gson_internal_bind_TypeAdapters_SHORT_TypeAdapter_5__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_INTEGER_TypeAdapter_6_read__unresolvedSignature__1_,
  f_com_google_gson_internal_bind_TypeAdapters_INTEGER_TypeAdapter_6_write__unresolvedSignature__2_,
  f_com_google_gson_internal_bind_TypeAdapters_INTEGER_TypeAdapter_6__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_INTEGER_TypeAdapter_7_read_java_util_concurrent_atomic_AtomicInteger,
  f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_INTEGER_TypeAdapter_7_write_void_com_google_gson_stream_JsonWriter_j,
  f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_INTEGER_TypeAdapter_7__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_BOOLEAN_TypeAdapter_8_read_java_util_concurrent_atomic_AtomicBoolean,
  f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_BOOLEAN_TypeAdapter_8_write_void_com_google_gson_stream_JsonWriter_j,
  f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_BOOLEAN_TypeAdapter_8__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_INTEGER_ARRAY_TypeAdapter_9_read_java_util_concurrent_atomic_AtomicI,
  f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_INTEGER_ARRAY_TypeAdapter_9_write_void_com_google_gson_stream_JsonWr,
  f_com_google_gson_internal_bind_TypeAdapters_ATOMIC_INTEGER_ARRAY_TypeAdapter_9__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_LONG_TypeAdapter_10_read__unresolvedSignature__1_,
  f_com_google_gson_internal_bind_TypeAdapters_LONG_TypeAdapter_10_write__unresolvedSignature__2_,
  f_com_google_gson_internal_bind_TypeAdapters_LONG_TypeAdapter_10__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_LONG_AS_STRING_TypeAdapter_11_read__unresolvedSignature__1_,
  f_com_google_gson_internal_bind_TypeAdapters_LONG_AS_STRING_TypeAdapter_11_write__unresolvedSignature__2_,
  f_com_google_gson_internal_bind_TypeAdapters_LONG_AS_STRING_TypeAdapter_11__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_CHARACTER_TypeAdapter_12_read__unresolvedSignature__1_,
  f_com_google_gson_internal_bind_TypeAdapters_CHARACTER_TypeAdapter_12_write__unresolvedSignature__2_,
  f_com_google_gson_internal_bind_TypeAdapters_CHARACTER_TypeAdapter_12__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_STRING_TypeAdapter_13_read__unresolvedSignature__1_,
  f_com_google_gson_internal_bind_TypeAdapters_STRING_TypeAdapter_13_write__unresolvedSignature__2_,
  f_com_google_gson_internal_bind_TypeAdapters_STRING_TypeAdapter_13__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_BIG_DECIMAL_TypeAdapter_14_read_java_math_BigDecimal_com_google_gson_stream,
  f_com_google_gson_internal_bind_TypeAdapters_BIG_DECIMAL_TypeAdapter_14_write_void_com_google_gson_stream_JsonWriter_jav,
  f_com_google_gson_internal_bind_TypeAdapters_BIG_DECIMAL_TypeAdapter_14__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_BIG_INTEGER_TypeAdapter_15_read_java_math_BigInteger_com_google_gson_stream,
  f_com_google_gson_internal_bind_TypeAdapters_BIG_INTEGER_TypeAdapter_15_write_void_com_google_gson_stream_JsonWriter_jav,
  f_com_google_gson_internal_bind_TypeAdapters_BIG_INTEGER_TypeAdapter_15__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_LAZILY_PARSED_NUMBER_TypeAdapter_16_read_com_google_gson_internal_LazilyPar,
  f_com_google_gson_internal_bind_TypeAdapters_LAZILY_PARSED_NUMBER_TypeAdapter_16_write_void_com_google_gson_stream_JsonW,
  f_com_google_gson_internal_bind_TypeAdapters_LAZILY_PARSED_NUMBER_TypeAdapter_16__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_STRING_BUILDER_TypeAdapter_17_read__unresolvedSignature__1_,
  f_com_google_gson_internal_bind_TypeAdapters_STRING_BUILDER_TypeAdapter_17_write__unresolvedSignature__2_,
  f_com_google_gson_internal_bind_TypeAdapters_STRING_BUILDER_TypeAdapter_17__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_STRING_BUFFER_TypeAdapter_18_read__unresolvedSignature__1_,
  f_com_google_gson_internal_bind_TypeAdapters_STRING_BUFFER_TypeAdapter_18_write__unresolvedSignature__2_,
  f_com_google_gson_internal_bind_TypeAdapters_STRING_BUFFER_TypeAdapter_18__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_URL_TypeAdapter_19_read_java_net_URL_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_bind_TypeAdapters_URL_TypeAdapter_19_write_void_com_google_gson_stream_JsonWriter_java_net_UR,
  f_com_google_gson_internal_bind_TypeAdapters_URL_TypeAdapter_19__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_URI_TypeAdapter_20_read_java_net_URI_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_bind_TypeAdapters_URI_TypeAdapter_20_write_void_com_google_gson_stream_JsonWriter_java_net_UR,
  f_com_google_gson_internal_bind_TypeAdapters_URI_TypeAdapter_20__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_INET_ADDRESS_TypeAdapter_21_read_java_net_InetAddress_com_google_gson_strea,
  f_com_google_gson_internal_bind_TypeAdapters_INET_ADDRESS_TypeAdapter_21_write_void_com_google_gson_stream_JsonWriter_ja,
  f_com_google_gson_internal_bind_TypeAdapters_INET_ADDRESS_TypeAdapter_21__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_UUID_TypeAdapter_22_read_java_util_UUID_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_bind_TypeAdapters_UUID_TypeAdapter_22_write_void_com_google_gson_stream_JsonWriter_java_util_,
  f_com_google_gson_internal_bind_TypeAdapters_UUID_TypeAdapter_22__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_CURRENCY_TypeAdapter_23_read_java_util_Currency_com_google_gson_stream_Json,
  f_com_google_gson_internal_bind_TypeAdapters_CURRENCY_TypeAdapter_23_write_void_com_google_gson_stream_JsonWriter_java_u,
  f_com_google_gson_internal_bind_TypeAdapters_CURRENCY_TypeAdapter_23__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_CALENDAR_IntegerFieldsTypeAdapter_24_create_java_util_Calendar_long___,
  f_com_google_gson_internal_bind_TypeAdapters_CALENDAR_IntegerFieldsTypeAdapter_24_integerValues_long___java_util_Calenda,
  f_com_google_gson_internal_bind_TypeAdapters_CALENDAR_IntegerFieldsTypeAdapter_24__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_LOCALE_TypeAdapter_25_read_java_util_Locale_com_google_gson_stream_JsonRead,
  f_com_google_gson_internal_bind_TypeAdapters_LOCALE_TypeAdapter_25_write_void_com_google_gson_stream_JsonWriter_java_uti,
  f_com_google_gson_internal_bind_TypeAdapters_LOCALE_TypeAdapter_25__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_atomicLongAdapter_TypeAdapter_0_read_java_util_concurrent_atomic_AtomicLong,
  f_com_google_gson_internal_bind_TypeAdapters_atomicLongAdapter_TypeAdapter_0_write_void_com_google_gson_stream_JsonWrite,
  f_com_google_gson_internal_bind_TypeAdapters_atomicLongAdapter_TypeAdapter_0__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_atomicLongArrayAdapter_TypeAdapter_0_read_java_util_concurrent_atomic_Atomi,
  f_com_google_gson_internal_bind_TypeAdapters_atomicLongArrayAdapter_TypeAdapter_0_write_void_com_google_gson_stream_Json,
  f_com_google_gson_internal_bind_TypeAdapters_atomicLongArrayAdapter_TypeAdapter_0__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_goog,
  f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_goog',
  f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0_toString__unresolvedSignature__0_,
  f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0__init__void__',
  f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_goog'',
  f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0_toString__unresolvedSignature__0_',
  f_com_google_gson_internal_bind_TypeAdapters_newFactory_TypeAdapterFactory_0__init__void__'',
  f_com_google_gson_internal_bind_TypeAdapters_newFactoryForMultipleTypes_TypeAdapterFactory_0_create_com_google_gson_Type,
  f_com_google_gson_internal_bind_TypeAdapters_newFactoryForMultipleTypes_TypeAdapterFactory_0_toString__unresolvedSignatu,
  f_com_google_gson_internal_bind_TypeAdapters_newFactoryForMultipleTypes_TypeAdapterFactory_0__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_TypeAdapterFactory_0_create_com_google_gson_TypeAda,
  f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_TypeAdapterFactory_0_toString__unresolvedSignature_,
  f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_TypeAdapterFactory_0__init__void__,
  f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_TypeAdapterFactory_0_create_TypeAdapter_0_write_voi,
  f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_TypeAdapterFactory_0_create_TypeAdapter_0_read_java,
  f_com_google_gson_internal_bind_TypeAdapters_newTypeHierarchyFactory_TypeAdapterFactory_0_create_TypeAdapter_0__init__vo,
  f_com_google_gson_internal_bind_util_ISO8601Utils__init__void__,
  f_com_google_gson_internal_bind_util_ISO8601Utils_format_java_lang_String_java_util_Date_,
  f_com_google_gson_internal_bind_util_ISO8601Utils_format_java_lang_String_java_util_Date_boolean_,
  f_com_google_gson_internal_bind_util_ISO8601Utils_format_java_lang_String_java_util_Date_boolean_java_util_TimeZone_,
  f_com_google_gson_internal_bind_util_ISO8601Utils_parse_java_util_Date_java_lang_String_java_text_ParsePosition_,
  f_com_google_gson_internal_bind_util_ISO8601Utils_checkOffset_boolean_java_lang_String_int_char_,
  f_com_google_gson_internal_bind_util_ISO8601Utils_parseInt_int_java_lang_String_int_int_,
  f_com_google_gson_internal_bind_util_ISO8601Utils_padInt_void_java_lang_StringBuilder_int_int_,
  f_com_google_gson_internal_bind_util_ISO8601Utils_indexOfNonDigit_int_java_lang_String_int_,
  f_com_google_gson_internal_bind_util_ISO8601Utils__clinit__void__,
  f_com_google_gson_internal_reflect_ReflectionHelper__init__void__,
  f_com_google_gson_internal_reflect_ReflectionHelper_getInaccessibleTroubleshootingSuffix_java_lang_String_java_lang_Exce,
  f_com_google_gson_internal_reflect_ReflectionHelper_makeAccessible_void_java_lang_reflect_AccessibleObject_,
  f_com_google_gson_internal_reflect_ReflectionHelper_getAccessibleObjectDescription_java_lang_String_java_lang_reflect_Ac,
  f_com_google_gson_internal_reflect_ReflectionHelper_fieldToString_java_lang_String_java_lang_reflect_Field_,
  f_com_google_gson_internal_reflect_ReflectionHelper_constructorToString_java_lang_String_java_lang_reflect_Constructor_,
  f_com_google_gson_internal_reflect_ReflectionHelper_appendExecutableParameters_void_java_lang_reflect_AccessibleObject_j,
  f_com_google_gson_internal_reflect_ReflectionHelper_isStatic_boolean_java_lang_Class_,
  f_com_google_gson_internal_reflect_ReflectionHelper_isAnonymousOrNonStaticLocal_boolean_java_lang_Class_,
  f_com_google_gson_internal_reflect_ReflectionHelper_tryMakeAccessible_java_lang_String_java_lang_reflect_Constructor_,
  f_com_google_gson_internal_reflect_ReflectionHelper_isRecord_boolean_java_lang_Class_,
  f_com_google_gson_internal_reflect_ReflectionHelper_getRecordComponentNames_java_lang_String___java_lang_Class_,
  f_com_google_gson_internal_reflect_ReflectionHelper_getAccessor_java_lang_reflect_Method_java_lang_Class_java_lang_refle,
  f_com_google_gson_internal_reflect_ReflectionHelper_getCanonicalRecordConstructor_java_lang_reflect_Constructor_java_lan,
  f_com_google_gson_internal_reflect_ReflectionHelper_createExceptionForUnexpectedIllegalAccess_java_lang_RuntimeException,
  f_com_google_gson_internal_reflect_ReflectionHelper_createExceptionForRecordReflectionException_java_lang_RuntimeExcepti,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordHelper_isRecord_boolean_java_lang_Class_,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordHelper_getRecordComponentNames_java_lang_String___java_lang_Cl,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordHelper_getCanonicalRecordConstructor_java_lang_reflect_Constru,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordHelper_getAccessor_java_lang_reflect_Method_java_lang_Class_ja,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordHelper__init__void__,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordSupportedHelper__init__void__,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordSupportedHelper_isRecord_boolean_java_lang_Class_,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordSupportedHelper_getRecordComponentNames_java_lang_String___jav,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordSupportedHelper_getCanonicalRecordConstructor_java_lang_reflec,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordSupportedHelper_getAccessor_java_lang_reflect_Method_java_lang,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordNotSupportedHelper_isRecord_boolean_java_lang_Class_,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordNotSupportedHelper_getRecordComponentNames_java_lang_String___,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordNotSupportedHelper_getCanonicalRecordConstructor_java_lang_ref,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordNotSupportedHelper_getAccessor_java_lang_reflect_Method_java_l,
  f_com_google_gson_internal_reflect_ReflectionHelper_RecordNotSupportedHelper__init__void__,
  f_com_google_gson_internal_sql_SqlDateTypeAdapter__init__void__,
  f_com_google_gson_internal_sql_SqlDateTypeAdapter_read_java_sql_Date_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_sql_SqlDateTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_sql_Date_,
  f_com_google_gson_internal_sql_SqlDateTypeAdapter__clinit__void__,
  f_com_google_gson_internal_sql_SqlDateTypeAdapter_FACTORY_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_go,
  f_com_google_gson_internal_sql_SqlDateTypeAdapter_FACTORY_TypeAdapterFactory_0__init__void__,
  f_com_google_gson_internal_sql_SqlTimeTypeAdapter__init__void__,
  f_com_google_gson_internal_sql_SqlTimeTypeAdapter_read_java_sql_Time_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_sql_SqlTimeTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_sql_Time_,
  f_com_google_gson_internal_sql_SqlTimeTypeAdapter__clinit__void__,
  f_com_google_gson_internal_sql_SqlTimeTypeAdapter_FACTORY_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_com_go,
  f_com_google_gson_internal_sql_SqlTimeTypeAdapter_FACTORY_TypeAdapterFactory_0__init__void__,
  f_com_google_gson_internal_sql_SqlTimestampTypeAdapter__init__void_com_google_gson_TypeAdapter_,
  f_com_google_gson_internal_sql_SqlTimestampTypeAdapter_read_java_sql_Timestamp_com_google_gson_stream_JsonReader_,
  f_com_google_gson_internal_sql_SqlTimestampTypeAdapter_write_void_com_google_gson_stream_JsonWriter_java_sql_Timestamp_,
  f_com_google_gson_internal_sql_SqlTimestampTypeAdapter__clinit__void__,
  f_com_google_gson_internal_sql_SqlTimestampTypeAdapter_FACTORY_TypeAdapterFactory_0_create_com_google_gson_TypeAdapter_c,
  f_com_google_gson_internal_sql_SqlTimestampTypeAdapter_FACTORY_TypeAdapterFactory_0__init__void__,
  f_com_google_gson_internal_sql_SqlTypesSupport__init__void__
] }

end Autoform.Generated