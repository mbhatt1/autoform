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
set_option maxRecDepth 8472

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
# PyMro — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.PyMro
open Autoform.Core

/-- `pymro_cases.py:<module>.Store.__init__`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Store___init__ : Func :=
  { name := "pymro_cases.py:<module>.Store.__init__"
  , params := []
  , body := (.setField (.name "self") "count" (.lit (.int 0))) }

/-- `pymro_cases.py:<module>.Store.lookup`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Store_lookup : Func :=
  { name := "pymro_cases.py:<module>.Store.lookup"
  , params := ["key"]
  , body := (.seq
            (.ifte (.binop "==" (.name "key") (.lit (.int 1))) (.ret (.lit (.str "one"))) .skip)
            (.ret (.mcall (.name "self") "on_missing" [(.name "key")]))) }

/-- `pymro_cases.py:<module>.Store.on_missing`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Store_on_missing : Func :=
  { name := "pymro_cases.py:<module>.Store.on_missing"
  , params := ["key"]
  , body := (.seq (.raise (.call "KeyError" [(.name "key")])) .skip) }

/-- `pymro_cases.py:<module>.Store.size`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Store_size : Func :=
  { name := "pymro_cases.py:<module>.Store.size"
  , params := []
  , body := (.seq
            (.setField
              (.name "self")
              "count"
              (.binop "+" (.field (.name "self") "count") (.lit (.int 1))))
            (.ret (.field (.name "self") "count"))) }

/-- `pymro_cases.py:<module>.DefaultStore.on_missing`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__DefaultStore_on_missing : Func :=
  { name := "pymro_cases.py:<module>.DefaultStore.on_missing"
  , params := ["key"]
  , body := (.ret (.tupleE [(.lit (.str "default")), (.name "key")])) }

/-- `pymro_cases.py:<module>.case_override_reached_from_base`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_override_reached_from_base : Func :=
  { name := "pymro_cases.py:<module>.case_override_reached_from_base"
  , params := []
  , body := (.seq
            (.assign "s" (.alloc "DefaultStore" []))
            (.seq .skip (.seq (.ret (.mcall (.name "s") "lookup" [(.lit (.int 7))])) .skip))) }

/-- `pymro_cases.py:<module>.case_base_method_unchanged`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_base_method_unchanged : Func :=
  { name := "pymro_cases.py:<module>.case_base_method_unchanged"
  , params := []
  , body := (.seq
            (.assign "s" (.alloc "Store" []))
            (.seq
              .skip
              (.seq
                (.tryCatch
                  (.ret (.mcall (.name "s") "lookup" [(.lit (.int 7))]))
                  "__exc"
                  (.ret (.lit (.str "KeyError"))))
                .skip))) }

/-- `pymro_cases.py:<module>.case_inherited_method`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_inherited_method : Func :=
  { name := "pymro_cases.py:<module>.case_inherited_method"
  , params := []
  , body := (.seq
            (.assign "s" (.alloc "DefaultStore" []))
            (.seq
              .skip
              (.seq
                (.expr (.mcall (.name "s") "size" []))
                (.seq .skip (.ret (.mcall (.name "s") "size" [])))))) }

/-- `pymro_cases.py:<module>.case_inherited_init`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_inherited_init : Func :=
  { name := "pymro_cases.py:<module>.case_inherited_init"
  , params := []
  , body := (.seq
            (.assign "s" (.alloc "DefaultStore" []))
            (.seq .skip (.seq (.ret (.field (.name "s") "count")) .skip))) }

/-- `pymro_cases.py:<module>.case_base_method_through_class_value`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_base_method_through_class_value : Func :=
  { name := "pymro_cases.py:<module>.case_base_method_through_class_value"
  , params := []
  , body := (.seq
            (.assign "s" (.alloc "DefaultStore" []))
            (.seq .skip (.seq (.ret (.mcall (.name "DefaultStore") "size" [(.name "s")])) .skip))) }

/-- `pymro_cases.py:<module>.Root.who`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Root_who : Func :=
  { name := "pymro_cases.py:<module>.Root.who"
  , params := []
  , body := (.ret (.boxContainer (.listE [(.lit (.str "Root"))]))) }

/-- `pymro_cases.py:<module>.Root.tag`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Root_tag : Func :=
  { name := "pymro_cases.py:<module>.Root.tag"
  , params := []
  , body := (.ret (.lit (.str "root"))) }

/-- `pymro_cases.py:<module>.Left.who`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Left_who : Func :=
  { name := "pymro_cases.py:<module>.Left.who"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" [(.lit (.str "Left")), (.name "self")]))
              (.assign "rest" (.mcall (.name "tmp0") "who" [])))
            (.seq
              .skip
              (.seq
                (.ret (.binop "+" (.boxContainer (.listE [(.lit (.str "Left"))])) (.name "rest")))
                (.seq .skip .skip)))) }

/-- `pymro_cases.py:<module>.Right.who`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Right_who : Func :=
  { name := "pymro_cases.py:<module>.Right.who"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" [(.lit (.str "Right")), (.name "self")]))
              (.assign "rest" (.mcall (.name "tmp0") "who" [])))
            (.seq
              .skip
              (.seq
                (.ret (.binop "+" (.boxContainer (.listE [(.lit (.str "Right"))])) (.name "rest")))
                (.seq .skip .skip)))) }

/-- `pymro_cases.py:<module>.Right.tag`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Right_tag : Func :=
  { name := "pymro_cases.py:<module>.Right.tag"
  , params := []
  , body := (.ret (.lit (.str "right"))) }

/-- `pymro_cases.py:<module>.Bottom.who`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Bottom_who : Func :=
  { name := "pymro_cases.py:<module>.Bottom.who"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" [(.lit (.str "Bottom")), (.name "self")]))
              (.assign "rest" (.mcall (.name "tmp0") "who" [])))
            (.seq
              .skip
              (.seq
                (.ret (.binop "+" (.boxContainer (.listE [(.lit (.str "Bottom"))])) (.name "rest")))
                (.seq .skip .skip)))) }

/-- `pymro_cases.py:<module>.case_diamond_mro_lookup`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_diamond_mro_lookup : Func :=
  { name := "pymro_cases.py:<module>.case_diamond_mro_lookup"
  , params := []
  , body := (.seq
            (.seq (.assign "tmp0" (.alloc "Bottom" [])) (.ret (.mcall (.name "tmp0") "tag" [])))
            (.seq .skip .skip)) }

/-- `pymro_cases.py:<module>.case_super_follows_instance_mro`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_super_follows_instance_mro : Func :=
  { name := "pymro_cases.py:<module>.case_super_follows_instance_mro"
  , params := []
  , body := (.seq
            (.seq (.assign "tmp0" (.alloc "Bottom" [])) (.ret (.mcall (.name "tmp0") "who" [])))
            (.seq .skip .skip)) }

/-- `pymro_cases.py:<module>.case_super_single`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_super_single : Func :=
  { name := "pymro_cases.py:<module>.case_super_single"
  , params := []
  , body := (.seq
            (.seq (.assign "tmp0" (.alloc "Left" [])) (.ret (.mcall (.name "tmp0") "who" [])))
            (.seq .skip .skip)) }

/-- `pymro_cases.py:<module>.Counter.__init__`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Counter___init__ : Func :=
  { name := "pymro_cases.py:<module>.Counter.__init__"
  , params := ["start"]
  , body := (.setField (.name "self") "n" (.name "start")) }

/-- `pymro_cases.py:<module>.StepCounter.__init__`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__StepCounter___init__ : Func :=
  { name := "pymro_cases.py:<module>.StepCounter.__init__"
  , params := ["start", "step"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "super" [(.lit (.str "StepCounter")), (.name "self")]))
              (.expr (.mcall (.name "tmp0") "__init__" [(.name "start")])))
            (.seq (.setField (.name "self") "step" (.name "step")) (.seq .skip .skip))) }

/-- `pymro_cases.py:<module>.StepCounter.bump`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__StepCounter_bump : Func :=
  { name := "pymro_cases.py:<module>.StepCounter.bump"
  , params := []
  , body := (.seq
            (.setField
              (.name "self")
              "n"
              (.binop "+" (.field (.name "self") "n") (.field (.name "self") "step")))
            (.ret (.field (.name "self") "n"))) }

/-- `pymro_cases.py:<module>.case_super_init_with_args`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_super_init_with_args : Func :=
  { name := "pymro_cases.py:<module>.case_super_init_with_args"
  , params := []
  , body := (.seq
            (.assign "c" (.alloc "StepCounter" [(.lit (.int 10)), (.lit (.int 3))]))
            (.seq
              .skip
              (.seq
                (.expr (.mcall (.name "c") "bump" []))
                (.seq .skip (.ret (.mcall (.name "c") "bump" [])))))) }

/-- `pymro_cases.py:<module>.Shelf.get`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Shelf_get : Func :=
  { name := "pymro_cases.py:<module>.Shelf.get"
  , params := ["k"]
  , body := (.ret (.tupleE [(.lit (.str "get")), (.name "k")])) }

/-- `pymro_cases.py:<module>.Shelf.make`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Shelf_make : Func :=
  { name := "pymro_cases.py:<module>.Shelf.make"
  , params := ["k"]
  , body := (.ret (.tupleE [(.lit (.str "make")), (.name "k")])) }

/-- `pymro_cases.py:<module>.case_staticmethod_through_instance`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_staticmethod_through_instance : Func :=
  { name := "pymro_cases.py:<module>.case_staticmethod_through_instance"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp0" (.alloc "Shelf" []))
              (.ret (.mcall (.name "tmp0") "make" [(.lit (.int 5))])))
            (.seq .skip .skip)) }

/-- `pymro_cases.py:<module>.case_class_attribute_alias`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_class_attribute_alias : Func :=
  { name := "pymro_cases.py:<module>.case_class_attribute_alias"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp0" (.alloc "Shelf" []))
              (.ret (.mcall (.name "tmp0") "fetch" [(.lit (.int 5))])))
            (.seq .skip .skip)) }

/-- `pymro_cases.py:<module>.Bag.__init__`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Bag___init__ : Func :=
  { name := "pymro_cases.py:<module>.Bag.__init__"
  , params := []
  , body := (.setField (.name "self") "v" (.lit (.int 1))) }

/-- `pymro_cases.py:<module>.Bag.__getitem__`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Bag___getitem__ : Func :=
  { name := "pymro_cases.py:<module>.Bag.__getitem__"
  , params := ["k"]
  , body := (.seq
            (.ifte
              (.binop "==" (.name "k") (.lit (.str "a")))
              (.ret (.field (.name "self") "v"))
              .skip)
            (.seq .skip (.raise (.call "KeyError" [(.name "k")])))) }

/-- `pymro_cases.py:<module>.Bag.__len__`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Bag___len__ : Func :=
  { name := "pymro_cases.py:<module>.Bag.__len__"
  , params := []
  , body := (.ret (.lit (.int 1))) }

/-- `pymro_cases.py:<module>.Bag.__iter__`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Bag___iter__ : Func :=
  { name := "pymro_cases.py:<module>.Bag.__iter__"
  , params := []
  , body := (.seq (.ret (.call "iter" [(.boxContainer (.listE [(.lit (.str "a"))]))])) .skip) }

/-- `pymro_cases.py:<module>.case_external_base_method`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_external_base_method : Func :=
  { name := "pymro_cases.py:<module>.case_external_base_method"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp0" (.alloc "Bag" []))
              (.ret (.mcall (.name "tmp0") "get" [(.lit (.str "a"))])))
            (.seq .skip .skip)) }

/-- `pymro_cases.py:<module>.case_own_method_before_external_base`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_own_method_before_external_base : Func :=
  { name := "pymro_cases.py:<module>.case_own_method_before_external_base"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp0" (.alloc "Bag" []))
              (.ret (.mcall (.name "tmp0") "__getitem__" [(.lit (.str "a"))])))
            (.seq .skip .skip)) }

/-- `pymro_cases.py:<module>.case_absent_method`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_absent_method : Func :=
  { name := "pymro_cases.py:<module>.case_absent_method"
  , params := []
  , body := (.seq
            (.tryCatch
              (.seq
                (.assign "tmp0" (.alloc "Store" []))
                (.ret (.mcall (.name "tmp0") "nonexistent" [])))
              "__exc"
              (.ret (.lit (.str "AttributeError"))))
            (.seq .skip .skip)) }

/-- `pymro_cases.py:<module>.make_base`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__make_base : Func :=
  { name := "pymro_cases.py:<module>.make_base"
  , params := []
  , body := (.seq (.ret (.name "Store")) .skip) }

/-- `pymro_cases.py:<module>.Dynamic.extra`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Dynamic_extra : Func :=
  { name := "pymro_cases.py:<module>.Dynamic.extra"
  , params := []
  , body := (.ret (.lit (.int 1))) }

/-- `pymro_cases.py:<module>.case_unresolvable_base`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_unresolvable_base : Func :=
  { name := "pymro_cases.py:<module>.case_unresolvable_base"
  , params := []
  , body := (.seq
            (.seq (.assign "tmp0" (.alloc "Dynamic" [])) (.ret (.mcall (.name "tmp0") "size" [])))
            (.seq .skip .skip)) }

/-- `pymro_cases.py:<module>.Holder.orphan_fn`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Holder_orphan_fn : Func :=
  { name := "pymro_cases.py:<module>.Holder.orphan_fn"
  , params := []
  , body := (.ret (.lit (.str "method"))) }

/-- `pymro_cases.py:<module>.Holder.scale`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Holder_scale : Func :=
  { name := "pymro_cases.py:<module>.Holder.scale"
  , params := ["x"]
  , body := (.ret (.binop "*" (.name "x") (.lit (.int 100)))) }

/-- `pymro_cases.py:<module>.case_unbound_name_is_not_a_method`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_unbound_name_is_not_a_method : Func :=
  { name := "pymro_cases.py:<module>.case_unbound_name_is_not_a_method"
  , params := []
  , body := (.seq
            (.tryCatch (.ret (.call "orphan_fn" [])) "__exc" (.ret (.lit (.str "NameError"))))
            .skip) }

/-- `pymro_cases.py:<module>.case_local_function_value_shadows_method`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_local_function_value_shadows_method : Func :=
  { name := "pymro_cases.py:<module>.case_local_function_value_shadows_method"
  , params := []
  , body := (.seq
            (.assign
              "scale"
              (.fnref "pymro_cases.py:<module>.case_local_function_value_shadows_method.<lambda>0"))
            (.seq (.ret (.call "scale" [(.lit (.int 4))])) .skip)) }

/-- `pymro_cases.py:<module>.case_local_function_value_shadows_method.<lambda>0`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_local_function_value_shadows_method__lambda_0 : Func :=
  { name := "pymro_cases.py:<module>.case_local_function_value_shadows_method.<lambda>0"
  , params := ["x"]
  , body := (.ret (.binop "+" (.name "x") (.lit (.int 1)))) }

/-- `pymro_cases.py:<module>.case_parameter_function_value`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_parameter_function_value : Func :=
  { name := "pymro_cases.py:<module>.case_parameter_function_value"
  , params := []
  , body := (.seq
            (.ret
              (.call
                "pymro_cases.py:<module>.apply_it"
                [ (.name "len")
                , (.boxContainer (.listE [(.lit (.int 1)), (.lit (.int 2)), (.lit (.int 3))])) ]))
            (.seq .skip .skip)) }

/-- `pymro_cases.py:<module>.apply_it`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__apply_it : Func :=
  { name := "pymro_cases.py:<module>.apply_it"
  , params := ["fn", "arg"]
  , body := (.ret (.call "fn" [(.name "arg")])) }

/-- `pymro_cases.py:<module>.case_module_global_read`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_module_global_read : Func :=
  { name := "pymro_cases.py:<module>.case_module_global_read"
  , params := []
  , body := (.seq (.ret (.binop "+" (.name "MODULE_LIMIT") (.lit (.int 1)))) .skip) }

/-- `pymro_cases.py:<module>.case_builtin_call`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_builtin_call : Func :=
  { name := "pymro_cases.py:<module>.case_builtin_call"
  , params := []
  , body := (.seq (.ret (.call "len" [(.lit (.str "abcd"))])) .skip) }

/-- `pymro_cases.py:<module>.Shape.area`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Shape_area : Func :=
  { name := "pymro_cases.py:<module>.Shape.area"
  , params := []
  , body := (.ret (.lit (.int 0))) }

/-- `pymro_cases.py:<module>.Shape.describe`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Shape_describe : Func :=
  { name := "pymro_cases.py:<module>.Shape.describe"
  , params := []
  , body := (.ret (.tupleE [(.lit (.str "shape")), (.mcall (.name "self") "area" [])])) }

/-- `pymro_cases.py:<module>.Square.__init__`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Square___init__ : Func :=
  { name := "pymro_cases.py:<module>.Square.__init__"
  , params := ["s"]
  , body := (.setField (.name "self") "s" (.name "s")) }

/-- `pymro_cases.py:<module>.Square.area`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Square_area : Func :=
  { name := "pymro_cases.py:<module>.Square.area"
  , params := []
  , body := (.ret (.binop "*" (.field (.name "self") "s") (.field (.name "self") "s"))) }

/-- `pymro_cases.py:<module>.case_abc_base_is_transparent`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_abc_base_is_transparent : Func :=
  { name := "pymro_cases.py:<module>.case_abc_base_is_transparent"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp0" (.alloc "Square" [(.lit (.int 3))]))
              (.ret (.mcall (.name "tmp0") "describe" [])))
            (.seq .skip .skip)) }

/-- `pymro_cases.py:<module>.Callbacks.handler`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Callbacks_handler : Func :=
  { name := "pymro_cases.py:<module>.Callbacks.handler"
  , params := []
  , body := (.ret (.lit (.str "method"))) }

/-- `pymro_cases.py:<module>.case_instance_attribute_shadows_method`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_instance_attribute_shadows_method : Func :=
  { name := "pymro_cases.py:<module>.case_instance_attribute_shadows_method"
  , params := []
  , body := (.seq
            (.assign "c" (.alloc "Callbacks" []))
            (.seq
              (.setField
                (.name "c")
                "handler"
                (.fnref "pymro_cases.py:<module>.case_instance_attribute_shadows_method.<lambda>1"))
              (.seq (.ret (.mcall (.name "c") "handler" [])) (.seq .skip .skip)))) }

/-- `pymro_cases.py:<module>.case_instance_attribute_shadows_method.<lambda>1`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_instance_attribute_shadows_method__lambda_1 : Func :=
  { name := "pymro_cases.py:<module>.case_instance_attribute_shadows_method.<lambda>1"
  , params := []
  , body := (.ret (.lit (.str "instance"))) }

/-- `pymro_cases.py:<module>.Grid.__init__`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Grid___init__ : Func :=
  { name := "pymro_cases.py:<module>.Grid.__init__"
  , params := []
  , body := (.setField (.name "self") "total" (.lit (.int 0))) }

/-- `pymro_cases.py:<module>.Grid.__setitem__`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__Grid___setitem__ : Func :=
  { name := "pymro_cases.py:<module>.Grid.__setitem__"
  , params := ["k", "v"]
  , body := (.setField
            (.name "self")
            "total"
            (.binop "+" (.field (.name "self") "total") (.name "v"))) }

/-- `pymro_cases.py:<module>.case_inherited_setitem`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module__case_inherited_setitem : Func :=
  { name := "pymro_cases.py:<module>.case_inherited_setitem"
  , params := []
  , body := (.seq
            (.assign "g" (.alloc "SubGrid" []))
            (.seq
              .skip
              (.seq
                (.setIndex (.name "g") (.lit (.int 1)) (.lit (.int 5)))
                (.seq
                  .skip
                  (.seq
                    (.setIndex (.name "g") (.lit (.int 2)) (.lit (.int 7)))
                    (.ret (.field (.name "g") "total"))))))) }

/-- `<module-objects>:<module>`  (from ``) -/
def f__module_objects___module_ : Func :=
  { name := "<module-objects>:<module>"
  , params := []
  , body := (.seq
            (.setGlobal "<module>pymro_cases.py" (.alloc "<module>pymro_cases.py" []))
            (.seq
              (.setField
                (.name "<module>pymro_cases.py")
                "apply_it"
                (.fnref "pymro_cases.py:<module>.apply_it"))
              (.seq
                (.setField
                  (.name "<module>pymro_cases.py")
                  "case_abc_base_is_transparent"
                  (.fnref "pymro_cases.py:<module>.case_abc_base_is_transparent"))
                (.seq
                  (.setField
                    (.name "<module>pymro_cases.py")
                    "case_absent_method"
                    (.fnref "pymro_cases.py:<module>.case_absent_method"))
                  (.seq
                    (.setField
                      (.name "<module>pymro_cases.py")
                      "case_base_method_through_class_value"
                      (.fnref "pymro_cases.py:<module>.case_base_method_through_class_value"))
                    (.seq
                      (.setField
                        (.name "<module>pymro_cases.py")
                        "case_base_method_unchanged"
                        (.fnref "pymro_cases.py:<module>.case_base_method_unchanged"))
                      (.seq
                        (.setField
                          (.name "<module>pymro_cases.py")
                          "case_builtin_call"
                          (.fnref "pymro_cases.py:<module>.case_builtin_call"))
                        (.seq
                          (.setField
                            (.name "<module>pymro_cases.py")
                            "case_class_attribute_alias"
                            (.fnref "pymro_cases.py:<module>.case_class_attribute_alias"))
                          (.seq
                            (.setField
                              (.name "<module>pymro_cases.py")
                              "case_diamond_mro_lookup"
                              (.fnref "pymro_cases.py:<module>.case_diamond_mro_lookup"))
                            (.seq
                              (.setField
                                (.name "<module>pymro_cases.py")
                                "case_external_base_method"
                                (.fnref "pymro_cases.py:<module>.case_external_base_method"))
                              (.seq
                                (.setField
                                  (.name "<module>pymro_cases.py")
                                  "case_inherited_init"
                                  (.fnref "pymro_cases.py:<module>.case_inherited_init"))
                                (.seq
                                  (.setField
                                    (.name "<module>pymro_cases.py")
                                    "case_inherited_method"
                                    (.fnref "pymro_cases.py:<module>.case_inherited_method"))
                                  (.seq
                                    (.setField
                                      (.name "<module>pymro_cases.py")
                                      "case_inherited_setitem"
                                      (.fnref "pymro_cases.py:<module>.case_inherited_setitem"))
                                    (.seq
                                      (.setField
                                        (.name "<module>pymro_cases.py")
                                        "case_instance_attribute_shadows_method"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_instance_attribute_shadows_method"))
                                      (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "case_local_function_value_shadows_method"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_local_function_value_shadows_method"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "case_module_global_read"
                                        (.fnref "pymro_cases.py:<module>.case_module_global_read"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "case_override_reached_from_base"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_override_reached_from_base"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "case_own_method_before_external_base"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_own_method_before_external_base"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "case_parameter_function_value"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_parameter_function_value"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "case_staticmethod_through_instance"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_staticmethod_through_instance"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "case_super_follows_instance_mro"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_super_follows_instance_mro"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "case_super_init_with_args"
                                        (.fnref "pymro_cases.py:<module>.case_super_init_with_args"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "case_super_single"
                                        (.fnref "pymro_cases.py:<module>.case_super_single"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "case_unbound_name_is_not_a_method"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_unbound_name_is_not_a_method"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "case_unresolvable_base"
                                        (.fnref "pymro_cases.py:<module>.case_unresolvable_base"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "make_base"
                                        (.fnref "pymro_cases.py:<module>.make_base"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Bag"
                                        (.fnref "pymro_cases.py:<module>.Bag<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Bottom"
                                        (.fnref "pymro_cases.py:<module>.Bottom<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Callbacks"
                                        (.fnref "pymro_cases.py:<module>.Callbacks<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Counter"
                                        (.fnref "pymro_cases.py:<module>.Counter<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "DefaultStore"
                                        (.fnref "pymro_cases.py:<module>.DefaultStore<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Dynamic"
                                        (.fnref "pymro_cases.py:<module>.Dynamic<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Grid"
                                        (.fnref "pymro_cases.py:<module>.Grid<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Holder"
                                        (.fnref "pymro_cases.py:<module>.Holder<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Left"
                                        (.fnref "pymro_cases.py:<module>.Left<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Right"
                                        (.fnref "pymro_cases.py:<module>.Right<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Root"
                                        (.fnref "pymro_cases.py:<module>.Root<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Shape"
                                        (.fnref "pymro_cases.py:<module>.Shape<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Shelf"
                                        (.fnref "pymro_cases.py:<module>.Shelf<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Square"
                                        (.fnref "pymro_cases.py:<module>.Square<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "StepCounter"
                                        (.fnref "pymro_cases.py:<module>.StepCounter<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "Store"
                                        (.fnref "pymro_cases.py:<module>.Store<meta>"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pymro_cases.py")
                                        "SubGrid"
                                        (.fnref "pymro_cases.py:<module>.SubGrid<meta>"))
                                        .skip))))))))))))))))))))))))))))))))))))))))))) }

/-- `pymro_cases.py:<module>`  (from `pymro_cases.py`) -/
def f_pymro_cases_py__module_ : Func :=
  { name := "pymro_cases.py:<module>"
  , params := []
  , body := (.seq
            (.setGlobal "iter" (.fnref "__builtin.iter"))
            (.seq
              (.setGlobal "len" (.fnref "__builtin.len"))
              (.seq
                (.setGlobal "staticmethod" (.fnref "__builtin.staticmethod"))
                (.seq
                  (.setGlobal "super" (.fnref "__builtin.super"))
                  (.seq
                    (.expr
                      (.lit
                        (.str "Differential fixture for Python method resolution and name scoping (STRATEGY.md §60).\n\nEvery `case_*` function takes no arguments. `tests/test_pymro_cpython.py` runs each one under\nCPython and compares the result with the value Core computes for the SAME source after the\nwhole pipeline -- `pysrc2cpg` -> `cartographer/export_ast.sc` -> `cartographer/render_lean.py`\n-> `Autoform/PyMroProgram.lean` -- pinned by `#guard_msgs` in `Autoform/PyMro.lean`.\n\nTwo rules are under test, both of which Core used to get wrong by matching names on their\nsuffix (docs/conformance.md finding 3):\n\n* a method is looked up along `type(obj).__mro__` (C3), so a subclass override wins over the\n  base's own method even when the base is the one calling it, and `super()` continues along\n  the MRO of the INSTANCE, not of the class it is written in;\n* a bare name is a local, else a module global, else a builtin -- never \"any function whose\n  qualified name ends in that name\".\n")))
                    (.seq
                      (.setGlobal "collections" (.fnref "<absent:external>collections"))
                      (.seq
                        (.setGlobal "ABC" (.fnref "<absent:external>abc"))
                        (.seq
                          (.seq
                            (.setGlobal "Store" (.fnref "pymro_cases.py:<module>.Store<meta>"))
                            (.expr (.fnref "pymro_cases.py:<module>.Store<meta>")))
                          (.seq
                            (.seq
                              (.setGlobal
                                "DefaultStore"
                                (.fnref "pymro_cases.py:<module>.DefaultStore<meta>"))
                              (.expr (.fnref "pymro_cases.py:<module>.DefaultStore<meta>")))
                            (.seq
                              (.setGlobal
                                "case_override_reached_from_base"
                                (.fnref "pymro_cases.py:<module>.case_override_reached_from_base"))
                              (.seq
                                (.setGlobal
                                  "case_base_method_unchanged"
                                  (.fnref "pymro_cases.py:<module>.case_base_method_unchanged"))
                                (.seq
                                  (.setGlobal
                                    "case_inherited_method"
                                    (.fnref "pymro_cases.py:<module>.case_inherited_method"))
                                  (.seq
                                    (.setGlobal
                                      "case_inherited_init"
                                      (.fnref "pymro_cases.py:<module>.case_inherited_init"))
                                    (.seq
                                      (.setGlobal
                                        "case_base_method_through_class_value"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_base_method_through_class_value"))
                                      (.seq
                                        (.seq
                                        (.setGlobal
                                        "Root"
                                        (.fnref "pymro_cases.py:<module>.Root<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.Root<meta>")))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "Left"
                                        (.fnref "pymro_cases.py:<module>.Left<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.Left<meta>")))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "Right"
                                        (.fnref "pymro_cases.py:<module>.Right<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.Right<meta>")))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "Bottom"
                                        (.fnref "pymro_cases.py:<module>.Bottom<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.Bottom<meta>")))
                                        (.seq
                                        (.setGlobal
                                        "case_diamond_mro_lookup"
                                        (.fnref "pymro_cases.py:<module>.case_diamond_mro_lookup"))
                                        (.seq
                                        (.setGlobal
                                        "case_super_follows_instance_mro"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_super_follows_instance_mro"))
                                        (.seq
                                        (.setGlobal
                                        "case_super_single"
                                        (.fnref "pymro_cases.py:<module>.case_super_single"))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "Counter"
                                        (.fnref "pymro_cases.py:<module>.Counter<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.Counter<meta>")))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "StepCounter"
                                        (.fnref "pymro_cases.py:<module>.StepCounter<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.StepCounter<meta>")))
                                        (.seq
                                        (.setGlobal
                                        "case_super_init_with_args"
                                        (.fnref "pymro_cases.py:<module>.case_super_init_with_args"))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "Shelf"
                                        (.fnref "pymro_cases.py:<module>.Shelf<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.Shelf<meta>")))
                                        (.seq
                                        (.setGlobal
                                        "case_staticmethod_through_instance"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_staticmethod_through_instance"))
                                        (.seq
                                        (.setGlobal
                                        "case_class_attribute_alias"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_class_attribute_alias"))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "Bag"
                                        (.fnref "pymro_cases.py:<module>.Bag<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.Bag<meta>")))
                                        (.seq
                                        (.setGlobal
                                        "case_external_base_method"
                                        (.fnref "pymro_cases.py:<module>.case_external_base_method"))
                                        (.seq
                                        (.setGlobal
                                        "case_own_method_before_external_base"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_own_method_before_external_base"))
                                        (.seq
                                        (.setGlobal
                                        "case_absent_method"
                                        (.fnref "pymro_cases.py:<module>.case_absent_method"))
                                        (.seq
                                        (.setGlobal
                                        "make_base"
                                        (.fnref "pymro_cases.py:<module>.make_base"))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "Dynamic"
                                        (.fnref "pymro_cases.py:<module>.Dynamic<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.Dynamic<meta>")))
                                        (.seq
                                        (.setGlobal
                                        "case_unresolvable_base"
                                        (.fnref "pymro_cases.py:<module>.case_unresolvable_base"))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "Holder"
                                        (.fnref "pymro_cases.py:<module>.Holder<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.Holder<meta>")))
                                        (.seq
                                        (.setGlobal
                                        "case_unbound_name_is_not_a_method"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_unbound_name_is_not_a_method"))
                                        (.seq
                                        (.setGlobal
                                        "case_local_function_value_shadows_method"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_local_function_value_shadows_method"))
                                        (.seq
                                        (.setGlobal
                                        "case_parameter_function_value"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_parameter_function_value"))
                                        (.seq
                                        (.setGlobal
                                        "apply_it"
                                        (.fnref "pymro_cases.py:<module>.apply_it"))
                                        (.seq
                                        (.setGlobal "MODULE_LIMIT" (.lit (.int 9)))
                                        (.seq
                                        (.setGlobal
                                        "case_module_global_read"
                                        (.fnref "pymro_cases.py:<module>.case_module_global_read"))
                                        (.seq
                                        (.setGlobal
                                        "case_builtin_call"
                                        (.fnref "pymro_cases.py:<module>.case_builtin_call"))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "Shape"
                                        (.fnref "pymro_cases.py:<module>.Shape<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.Shape<meta>")))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "Square"
                                        (.fnref "pymro_cases.py:<module>.Square<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.Square<meta>")))
                                        (.seq
                                        (.setGlobal
                                        "case_abc_base_is_transparent"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_abc_base_is_transparent"))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "Callbacks"
                                        (.fnref "pymro_cases.py:<module>.Callbacks<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.Callbacks<meta>")))
                                        (.seq
                                        (.setGlobal
                                        "case_instance_attribute_shadows_method"
                                        (.fnref
                                        "pymro_cases.py:<module>.case_instance_attribute_shadows_method"))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "Grid"
                                        (.fnref "pymro_cases.py:<module>.Grid<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.Grid<meta>")))
                                        (.seq
                                        (.seq
                                        (.setGlobal
                                        "SubGrid"
                                        (.fnref "pymro_cases.py:<module>.SubGrid<meta>"))
                                        (.expr (.fnref "pymro_cases.py:<module>.SubGrid<meta>")))
                                        (.seq
                                        (.setGlobal
                                        "case_inherited_setitem"
                                        (.fnref "pymro_cases.py:<module>.case_inherited_setitem"))
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := [f__module_objects___module_, f_pymro_cases_py__module_]

/-- Source dialect: `.python` (integer division/modulo convention).

`pyClasses` is the class table: methods resolve along the C3 MRO, and bare
names by Python scoping (STRATEGY.md §60). -/
def program : Program := { dialect := .python, pyClasses := some [{ name := "Bag", bases := ["<ext>collections.abc.Mapping"], attrs := [] }, { name := "Bottom", bases := ["Left", "Right"], attrs := [] }, { name := "Callbacks", bases := [], attrs := [] }, { name := "Counter", bases := [], attrs := [] }, { name := "DefaultStore", bases := ["Store"], attrs := [] }, { name := "Grid", bases := [], attrs := [] }, { name := "Holder", bases := [], attrs := [] }, { name := "Left", bases := ["Root"], attrs := [] }, { name := "Right", bases := ["Root"], attrs := [] }, { name := "Root", bases := [], attrs := [] }, { name := "Shape", bases := [], attrs := [] }, { name := "Shelf", bases := [], attrs := ["fetch"] }, { name := "Square", bases := ["Shape"], attrs := [] }, { name := "StepCounter", bases := ["Counter"], attrs := [] }, { name := "Store", bases := [], attrs := [] }, { name := "SubGrid", bases := ["Grid"], attrs := [] }], funcs := [
  f_pymro_cases_py__module__Store___init__,
  f_pymro_cases_py__module__Store_lookup,
  f_pymro_cases_py__module__Store_on_missing,
  f_pymro_cases_py__module__Store_size,
  f_pymro_cases_py__module__DefaultStore_on_missing,
  f_pymro_cases_py__module__case_override_reached_from_base,
  f_pymro_cases_py__module__case_base_method_unchanged,
  f_pymro_cases_py__module__case_inherited_method,
  f_pymro_cases_py__module__case_inherited_init,
  f_pymro_cases_py__module__case_base_method_through_class_value,
  f_pymro_cases_py__module__Root_who,
  f_pymro_cases_py__module__Root_tag,
  f_pymro_cases_py__module__Left_who,
  f_pymro_cases_py__module__Right_who,
  f_pymro_cases_py__module__Right_tag,
  f_pymro_cases_py__module__Bottom_who,
  f_pymro_cases_py__module__case_diamond_mro_lookup,
  f_pymro_cases_py__module__case_super_follows_instance_mro,
  f_pymro_cases_py__module__case_super_single,
  f_pymro_cases_py__module__Counter___init__,
  f_pymro_cases_py__module__StepCounter___init__,
  f_pymro_cases_py__module__StepCounter_bump,
  f_pymro_cases_py__module__case_super_init_with_args,
  f_pymro_cases_py__module__Shelf_get,
  f_pymro_cases_py__module__Shelf_make,
  f_pymro_cases_py__module__case_staticmethod_through_instance,
  f_pymro_cases_py__module__case_class_attribute_alias,
  f_pymro_cases_py__module__Bag___init__,
  f_pymro_cases_py__module__Bag___getitem__,
  f_pymro_cases_py__module__Bag___len__,
  f_pymro_cases_py__module__Bag___iter__,
  f_pymro_cases_py__module__case_external_base_method,
  f_pymro_cases_py__module__case_own_method_before_external_base,
  f_pymro_cases_py__module__case_absent_method,
  f_pymro_cases_py__module__make_base,
  f_pymro_cases_py__module__Dynamic_extra,
  f_pymro_cases_py__module__case_unresolvable_base,
  f_pymro_cases_py__module__Holder_orphan_fn,
  f_pymro_cases_py__module__Holder_scale,
  f_pymro_cases_py__module__case_unbound_name_is_not_a_method,
  f_pymro_cases_py__module__case_local_function_value_shadows_method,
  f_pymro_cases_py__module__case_local_function_value_shadows_method__lambda_0,
  f_pymro_cases_py__module__case_parameter_function_value,
  f_pymro_cases_py__module__apply_it,
  f_pymro_cases_py__module__case_module_global_read,
  f_pymro_cases_py__module__case_builtin_call,
  f_pymro_cases_py__module__Shape_area,
  f_pymro_cases_py__module__Shape_describe,
  f_pymro_cases_py__module__Square___init__,
  f_pymro_cases_py__module__Square_area,
  f_pymro_cases_py__module__case_abc_base_is_transparent,
  f_pymro_cases_py__module__Callbacks_handler,
  f_pymro_cases_py__module__case_instance_attribute_shadows_method,
  f_pymro_cases_py__module__case_instance_attribute_shadows_method__lambda_1,
  f_pymro_cases_py__module__Grid___init__,
  f_pymro_cases_py__module__Grid___setitem__,
  f_pymro_cases_py__module__case_inherited_setitem,
  f__module_objects___module_,
  f_pymro_cases_py__module_
] }

end Autoform.Generated.PyMro