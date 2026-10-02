import Autoform.PyMroProgram
import Autoform.PyScoping

/-!
# Python method resolution and name scoping, checked against CPython (STRATEGY.md §62)

Two rules Core used to approximate by matching names on their suffix
(`docs/conformance.md`, finding 3):

* **Methods** are looked up along `type(obj).__mro__`, the C3 linearisation of the class
  table the exporter now records (`Program.pyClasses`), and `super()` continues along the
  MRO of the *instance*. Legacy resolution (`Ctx.resolveMethodLegacy`) took the receiver
  class's own method if it had one, else **any** unique function with that short name — so
  for a subclass Core did not know (the cachetools suite's `DefaultCache`), `Cache.__getitem__`
  called `Cache.__missing__` where CPython calls the subclass's override.
* **Bare names** are local, else module global, else builtin. Legacy resolution consulted
  the function table by suffix *before* the environment, so an unbound `f` reached any
  `….f`, including a method of an unrelated class.

Both switch on only for a Python program that carries a class table, so no corpus exported
before this changes meaning. Where the table does not determine the answer — a class it does
not contain, a base from outside the corpus, a class-body binding that is not a `def` — the
answer is a named hole (`mro:*`, `name:unbound:*`), never a guess.

Section 1 states the rules on small hand-written programs. Section 2 is end-to-end:
`Autoform/PyMroProgram.lean` is the rendered export of
`tests/fixtures/pymro/pymro_cases.py`, every `case_*` function is run here and pinned with
`#guard_msgs`, and `tests/test_pymro_cpython.py` runs the same functions under CPython and
fails unless each pin is CPython's value or a hole that file lists with its reason.
-/

namespace Autoform.Core
namespace PyMro

/-! ## 1. The rules, on hand-written programs

The cachetools shape: `Cache.__getitem__` calls `self.__missing__(k)`, and a subclass
overrides `__missing__`. -/

def fGet : Func :=
  { name := "m.py:<module>.Cache.__getitem__", params := ["k"]
  , body := .ret (.mcall (.name "self") "__missing__" [.name "k"]) }

def fMissing : Func :=
  { name := "m.py:<module>.Cache.__missing__", params := ["k"]
  , body := .raise (.lit (.str "KeyError")) }

def fSubMissing : Func :=
  { name := "m.py:<module>.DefaultCache.__missing__", params := ["k"]
  , body := .ret (.lit (.int 42)) }

/-- `DefaultCache()[1]` -/
def fRun : Func :=
  { name := "m.py:<module>.run", params := []
  , body := .ret (.mcall (.alloc "DefaultCache" []) "__getitem__" [.lit (.int 1)]) }

/-- The subclass is defined OUTSIDE the translated program (a test suite's class). -/
def progOutside (classes : Option (List PyClass)) : Program :=
  { dialect := .python, funcs := [fGet, fMissing, fRun], pyClasses := classes }

/-- The subclass is part of the program. -/
def progInside : Program :=
  { dialect := .python, funcs := [fGet, fMissing, fSubMissing, fRun]
  , pyClasses := some [{ name := "Cache", bases := [] },
                       { name := "DefaultCache", bases := ["Cache"] }] }

/-! Legacy resolution, the wrong answer: CPython runs the subclass's `__missing__`; Core
ran `Cache.__missing__` and raised. This is how the three cachetools divergences arose. -/
/-- info: Autoform.Core.EResult.exn (Autoform.Core.Val.str "KeyError") -/
#guard_msgs in #eval runFunc (progOutside none) 40 "m.py:<module>.run" []

/-! With a class table, a class Core does not know is a hole, not a guess. -/
/-- info: Autoform.Core.EResult.hole "mro:unknown-class:DefaultCache" -/
#guard_msgs in #eval runFunc (progOutside (some [{ name := "Cache", bases := [] }])) 40
  "m.py:<module>.run" []

/-! And a class it does know dispatches along the MRO: `__getitem__` is inherited from
`Cache`, and the `self.__missing__` it makes reaches the override. -/
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 42) -/
#guard_msgs in #eval runFunc progInside 40 "m.py:<module>.run" []

/-! C3 itself. `class D(B, C)`, `class B(A)`, `class C(A)`: `D, B, C, A` — not the
depth-first `D, B, A, C`. And an inconsistent order (`class X(A, B)` with `B(A)`) has no
linearisation: CPython raises `TypeError` at class creation. -/

def ctxDiamond : Ctx :=
  { dialect := .python, table := []
  , pyClasses := some [{ name := "A", bases := [] }, { name := "B", bases := ["A"] },
                       { name := "C", bases := ["A"] }, { name := "D", bases := ["B", "C"] },
                       { name := "X", bases := ["A", "B"] },
                       { name := "E", bases := ["B", "<ext>abc.Mapping"] }] }

/-- info: some ["D", "B", "C", "A"] -/
#guard_msgs in #eval ctxDiamond.mro "D"

/-- info: none -/
#guard_msgs in #eval ctxDiamond.mro "X"

/-! An external base is a leaf of the linearisation; lookup stops there with a hole. -/
/-- info: some ["E", "B", "A", "<ext>abc.Mapping"] -/
#guard_msgs in #eval ctxDiamond.mro "E"

/-- info: Autoform.Core.MLookup.hole "mro:external-base:abc.Mapping.get" -/
#guard_msgs in #eval ctxDiamond.lookupMethod "E" "get"

/-! Bare names. `orphan()` where the only `orphan` is a method of some class: CPython raises
`NameError`. Legacy resolution found the method by suffix and ran it. -/

def fOrphan : Func :=
  { name := "m.py:<module>.Holder.orphan", params := [], body := .ret (.lit (.str "method")) }

def fCallOrphan : Func :=
  { name := "m.py:<module>.f", params := [], body := .ret (.call "orphan" []) }

def fReadOrphan : Func :=
  { name := "m.py:<module>.g", params := [], body := .ret (.name "orphan") }

def progNames (classes : Option (List PyClass)) : Program :=
  { dialect := .python, funcs := [fOrphan, fCallOrphan, fReadOrphan], pyClasses := classes }

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.str "method") -/
#guard_msgs in #eval runFunc (progNames none) 40 "m.py:<module>.f" []

/-- info: Autoform.Core.EResult.hole "call:orphan" -/
#guard_msgs in #eval runFunc (progNames (some [])) 40 "m.py:<module>.f" []

/-- info: Autoform.Core.EResult.hole "name:unbound:orphan" -/
#guard_msgs in #eval runFunc (progNames (some [])) 40 "m.py:<module>.g" []

/-- Non-Python programs are untouched by a class table: the rules are Python's. -/
theorem pyStrict_only_python (t : List PyClass) :
    ({ dialect := .cLike, table := [], pyClasses := some t } : Ctx).pyStrict = false := rfl

/-! ## 2. End to end: the exported fixture, pinned, and compared with CPython

`pyRun` prints a result in the canonical text `tests/test_pymro_cpython.py` produces from
the CPython value, so the comparison is string equality on both sides. -/

open Autoform.Generated.PyMro in
def pyRun (c : String) : String :=
  PyScoping.showR (runMain program 600 moduleInits ("pymro_cases.py:<module>." ++ c) [])

-- CPython: ('shape', 9)
/-- info: "('shape', 9)" -/
#guard_msgs in #eval pyRun "case_abc_base_is_transparent"

-- CPython: 'AttributeError'
/-- info: "hole mcall:Store.nonexistent" -/
#guard_msgs in #eval pyRun "case_absent_method"

-- CPython: 1
/-- info: "1" -/
#guard_msgs in #eval pyRun "case_base_method_through_class_value"

-- CPython: 'KeyError'
/-- info: "'KeyError'" -/
#guard_msgs in #eval pyRun "case_base_method_unchanged"

-- CPython: 4
/-- info: "4" -/
#guard_msgs in #eval pyRun "case_builtin_call"

-- CPython: ('get', 5)
/-- info: "hole mro:class-attribute:Shelf.fetch" -/
#guard_msgs in #eval pyRun "case_class_attribute_alias"

-- CPython: 'right'
/-- info: "'right'" -/
#guard_msgs in #eval pyRun "case_diamond_mro_lookup"

-- CPython: 1
/-- info: "hole mro:external-base:collections.abc.Mapping.get" -/
#guard_msgs in #eval pyRun "case_external_base_method"

-- CPython: 0
/-- info: "0" -/
#guard_msgs in #eval pyRun "case_inherited_init"

-- CPython: 2
/-- info: "2" -/
#guard_msgs in #eval pyRun "case_inherited_method"

-- CPython: 12
/-- info: "12" -/
#guard_msgs in #eval pyRun "case_inherited_setitem"

-- CPython: 'instance'
/-- info: "hole mcall:Callbacks.handler:instance-attribute" -/
#guard_msgs in #eval pyRun "case_instance_attribute_shadows_method"

-- CPython: 5
/-- info: "5" -/
#guard_msgs in #eval pyRun "case_local_function_value_shadows_method"

-- CPython: 10
/-- info: "10" -/
#guard_msgs in #eval pyRun "case_module_global_read"

-- CPython: ('default', 7)
/-- info: "('default', 7)" -/
#guard_msgs in #eval pyRun "case_override_reached_from_base"

-- CPython: 1
/-- info: "1" -/
#guard_msgs in #eval pyRun "case_own_method_before_external_base"

-- CPython: 3
/-- info: "3" -/
#guard_msgs in #eval pyRun "case_parameter_function_value"

-- CPython: ('make', 5)
/-- info: "('make', 5)" -/
#guard_msgs in #eval pyRun "case_staticmethod_through_instance"

-- CPython: ['Bottom', 'Left', 'Right', 'Root']
/-- info: "['Bottom', 'Left', 'Right', 'Root']" -/
#guard_msgs in #eval pyRun "case_super_follows_instance_mro"

-- CPython: 16
/-- info: "16" -/
#guard_msgs in #eval pyRun "case_super_init_with_args"

-- CPython: ['Left', 'Root']
/-- info: "['Left', 'Root']" -/
#guard_msgs in #eval pyRun "case_super_single"

-- CPython: 'NameError'
/-- info: "hole call:orphan_fn" -/
#guard_msgs in #eval pyRun "case_unbound_name_is_not_a_method"

-- CPython: 1
/-- info: "hole mro:unknown-class:Dynamic" -/
#guard_msgs in #eval pyRun "case_unresolvable_base"

end PyMro
end Autoform.Core
