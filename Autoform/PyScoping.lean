import Autoform.PyScopingProgram

/-!
# Python calling convention and scoping, checked against CPython (STRATEGY.md §58)

Four constructs that used to be holes or — worse — silently wrong:

* **default parameter values** (`def f(b=1)`): `Func.defaults`. `pysrc2cpg` drops the
  default expression entirely, so the exporter reads it back from the source text. A
  literal default (`None`, numbers, plain strings, `True`/`False`, `()`) is bound on every
  call that omits it — indistinguishable from CPython's evaluate-once rule, because a
  literal denotes an immutable value with no identity Core can observe. Any other default
  (`acc=[]`, `t=time.monotonic`, `cache_setitem=Cache.__setitem__`) is the hole
  `param:default-nonliteral`, raised only by a call that actually needs it: CPython
  evaluates it once, at `def` time, and re-evaluating it per call would be wrong exactly
  where it matters (the mutable-default aliasing every Python programmer meets once).
* **keyword-only parameters** (`def f(a, *, b)`, `def f(*args, key=None)`): `Func.kwonly`.
  Before, `f(*args, key=None)` called as `f(1, 2)` bound `key = 2`.
* **positional-only parameters** (`def f(a, /)`): `Func.posonly`. A keyword naming one
  goes to `**kwargs` or raises `TypeError`, as in CPython.
* **`nonlocal` writes**: by cell conversion in the exporter (`cellsOwnedBy` in
  `cartographer/export_ast.sc`). The owner allocates the variable as a one-field heap
  cell (`Expr.boxNew`), and every read and write — in the owner and in every closure —
  goes through it, so a write from one closure is seen by the owner and by every other
  closure. Making this reachable needed one Core change: a closure held in a local
  variable is now applied *with its environment* when called by name (`Expr.call`).
* **starred assignment** (`a, *b, c = xs`): `Stdlib.unpackEx`, which materialises any
  iterable, binds the starred name to a LIST, and raises `ValueError` when too short.
  Making Joern's own lowering of it correct needed a second Core fix: `xs[-1]` returned
  the FIRST element (`Int.toNat (-1) = 0`).

Section 1 states the Core rules on small hand-written programs, as kernel-checked
theorems. Section 2 is end-to-end: `Autoform/PyScopingProgram.lean` is the rendered export
of `tests/fixtures/pyscoping/pyscoping_cases.py`, every `case_*` function of it is run here
and pinned with `#guard_msgs`, and `tests/test_pyscoping_cpython.py` runs the same
functions under CPython and fails if any pin is not CPython's value — or, for the two
documented `param:default-nonliteral` cases, not that hole.
-/

namespace Autoform.Core
namespace PyScoping

/-! ## 1. The rules, on hand-written programs -/

/-- `def d(a, b=10): return (a, b)` -/
def fD : Func :=
  { name := "d", params := ["a", "b"], defaults := [("b", .lit (.int 10))]
  , body := .ret (.tupleE [.name "a", .name "b"]) }

/-- `def m(x, acc=[]): return acc` — a default Core does not evaluate. -/
def fM : Func :=
  { name := "m", params := ["x", "acc"], defaults := [("acc", .hole "param:default-nonliteral")]
  , body := .ret (.name "acc") }

/-- `def k(a, *, b=2): return (a, b)` -/
def fK : Func :=
  { name := "k", params := ["a", "b"], kwonly := ["b"], defaults := [("b", .lit (.int 2))]
  , body := .ret (.tupleE [.name "a", .name "b"]) }

/-- `def v(*args, key=None): return (args, key)` -/
def fV : Func :=
  { name := "v", params := ["args", "key"], vararg := some "args", kwonly := ["key"]
  , defaults := [("key", .lit .unit)]
  , body := .ret (.tupleE [.name "args", .name "key"]) }

/-- `def p(a, /, **kw): return (a, kw)` -/
def fP : Func :=
  { name := "p", params := ["a", "kw"], posonly := ["a"], kwarg := some "kw"
  , body := .ret (.tupleE [.name "a", .name "kw"]) }

/-- `def q(a, /): return a` -/
def fQ : Func := { name := "q", params := ["a"], posonly := ["a"], body := .ret (.name "a") }

def callerU (nm : String) (e : Expr) : Func := { name := nm, params := [], body := .ret e }

def progU : Program := { dialect := .python, funcs :=
  [ fD, fM, fK, fV, fP, fQ
  , callerU "kw_b"   (.call "k" [.lit (.int 1), .kwargE "b" (.lit (.int 5))])
  , callerU "v12"    (.call "v" [.lit (.int 1), .lit (.int 2)])
  , callerU "p_kw"   (.call "p" [.lit (.int 1), .kwargE "a" (.lit (.int 2))])
  , callerU "q_kw"   (.call "q" [.kwargE "a" (.lit (.int 1))])
  , callerU "neg1"   (.index (.listE [.lit (.int 1), .lit (.int 2), .lit (.int 3)]) (.lit (.int (-1))))
  , callerU "neg4"   (.index (.tupleE [.lit (.int 1), .lit (.int 2), .lit (.int 3)]) (.lit (.int (-4))))
  ] }

/-- An omitted parameter with a literal default sees the default. -/
theorem literal_default_is_bound :
    runFunc progU 40 "d" [.int 1] = .val (.tuple [.int 1, .int 10]) := by rfl

/-- A supplied argument shadows its default. -/
theorem supplied_argument_shadows_default :
    runFunc progU 40 "d" [.int 1, .int 2] = .val (.tuple [.int 1, .int 2]) := by rfl

/-- A default Core cannot evaluate is a hole on the call that needs it, and only there. -/
theorem nonliteral_default_holes_only_when_needed :
    runFunc progU 40 "m" [.int 1] = .hole "param:default-nonliteral" ∧
    runFunc progU 40 "m" [.int 1, .list []] = .val (.list []) := ⟨rfl, rfl⟩

/-- That hole is a hole of the function, so the ledger counts it statically. -/
theorem nonliteral_default_is_counted : fM.holes = ["param:default-nonliteral"] := by rfl

/-- A keyword-only parameter cannot be filled positionally (CPython: `TypeError: k()
takes 1 positional argument but 2 were given`)... -/
theorem kwonly_rejects_positional :
    runFunc progU 40 "k" [.int 1, .int 2] = .exn (.str "TypeError") := by rfl

/-- ...is bound by keyword... -/
theorem kwonly_binds_by_keyword :
    runFunc progU 40 "kw_b" [] = .val (.tuple [.int 1, .int 5]) := by rfl

/-- ...and, after `*args`, no longer swallows a positional argument: `v(1, 2)` is
`((1, 2), None)`. This used to bind `key = 2`. -/
theorem kwonly_after_varargs :
    runFunc progU 40 "v12" [] = .val (.tuple [.tuple [.int 1, .int 2], .unit]) := by rfl

/-- A keyword naming a positional-only parameter goes to `**kwargs` (`p(1, a=2)` is
`(1, {'a': 2})`)... -/
theorem posonly_name_goes_to_kwargs :
    runFunc progU 40 "p_kw" [] = .val (.tuple [.int 1, .dict [(.str "a", .int 2)]]) := by rfl

/-- ...or, without one, is a `TypeError`. -/
theorem posonly_keyword_rejected :
    runFunc progU 40 "q_kw" [] = .exn (.str "TypeError") := by rfl

/-- `xs[-1]` is the LAST element. -/
theorem negative_index_counts_from_the_end :
    runFunc progU 40 "neg1" [] = .val (.int 3) := by rfl

/-- And out of range from the end is `IndexError`, not the first element. -/
theorem negative_index_out_of_range :
    runFunc progU 40 "neg4" [] = .exn (.str "IndexError") := by rfl

/-- `a, *b, c = (1, 2, 3, 4)`: the starred name is a LIST, even from a tuple. -/
theorem unpackEx_middle :
    Stdlib.unpackEx [] [.tuple [.int 1, .int 2, .int 3, .int 4], .int 1, .int 1]
      = some ([], .val (.tuple [.int 1, .list [.int 2, .int 3], .int 4])) := by rfl

/-- `a, *b, c = [1]`: too few values is `ValueError`. -/
theorem unpackEx_too_short :
    Stdlib.unpackEx [] [.list [.int 1], .int 1, .int 1] = some ([], .exn (.str "ValueError")) := by
  rfl

/-- `a, *b = 5`: `TypeError`. -/
theorem unpackEx_noniterable :
    Stdlib.unpackEx [] [.int 5, .int 1, .int 0] = some ([], .exn (.str "TypeError")) := by rfl

/-- An object is not answered: whether it is iterable depends on its class. -/
theorem unpackEx_object_unanswered :
    Stdlib.unpackEx [] [.ref 0, .int 1, .int 0] = none := by rfl

/-! ### Cell semantics, in Core directly

What the exporter emits for
```python
def outer():
    n = 0
    def inc():
        nonlocal n
        n += 1
    inc(); inc()
    return n
```
The write in `inc` reaches `outer`'s `n` because both hold the same cell. -/

def fOuter : Func :=
  { name := "outer", params := []
  , body := .seq (.assign "n" (.boxNew (.lit .unit)))
           (.seq (.setField (.name "n") "v" (.lit (.int 0)))
           (.seq (.assign "inc" (.closure "outer.inc"))
           (.seq (.expr (.call "inc" []))
           (.seq (.expr (.call "inc" []))
                 (.ret (.field (.name "n") "v")))))) }

def fInc : Func :=
  { name := "outer.inc", params := []
  , body := .setField (.name "n") "v" (.binop "+" (.field (.name "n") "v") (.lit (.int 1))) }

def progCell : Program := { dialect := .python, funcs := [fOuter, fInc] }

theorem nonlocal_write_is_seen_by_the_owner :
    runFunc progCell 40 "outer" [] = .val (.int 2) := by rfl

/-! ## 2. End to end: the exported fixture, pinned, and compared with CPython

`pyRun` prints a result in the canonical text `tests/test_pyscoping_cpython.py` produces
from the CPython value, so the comparison is string equality on both sides. -/

open Autoform.Generated.PyScoping in
/-- A Core value as Python would `repr` it, for the shapes the fixture returns. Fuelled
rather than `partial`, so that it stays an ordinary total function. -/
def showV : Nat → Val → String
  | 0, _ => "…"
  | _ + 1, .int i => toString i
  | _ + 1, .str s => "'" ++ s ++ "'"
  | _ + 1, .bool b => if b then "True" else "False"
  | _ + 1, .unit => "None"
  | _ + 1, .float f => s!"float(bits={f.bits})"
  | n + 1, .tuple [v] => "(" ++ showV n v ++ ",)"
  | n + 1, .tuple vs => "(" ++ ", ".intercalate (vs.map (showV n)) ++ ")"
  | n + 1, .list vs => "[" ++ ", ".intercalate (vs.map (showV n)) ++ "]"
  | n + 1, .dict kvs =>
      "{" ++ ", ".intercalate (kvs.map fun kv => showV n kv.1 ++ ": " ++ showV n kv.2) ++ "}"
  | _ + 1, _ => "<unprintable>"

def showR : EResult → String
  | .val v          => showV 50 v
  | .exn (.str e)   => "raise " ++ e
  | .exn v          => "raise " ++ showV 50 v
  | .hole l         => "hole " ++ l
  | .outOfFuel      => "outOfFuel"

open Autoform.Generated.PyScoping in
def pyRun (c : String) : String :=
  showR (runMain program 400 moduleInits ("pyscoping_cases.py:<module>." ++ c) [])

-- CPython: (1, 10, None, 's', True, (), -3, float(bits=4602678819172646912))
/-- info: "(1, 10, None, 's', True, (), -3, float(bits=4602678819172646912))" -/
#guard_msgs in #eval pyRun "case_default_all"

-- CPython: (1, 2, None, 't', True, (), -3, float(bits=4602678819172646912))
/-- info: "(1, 2, None, 't', True, (), -3, float(bits=4602678819172646912))" -/
#guard_msgs in #eval pyRun "case_default_some"

-- CPython: (5, 10, None, 's', True, (), 7, float(bits=4602678819172646912))
/-- info: "(5, 10, None, 's', True, (), 7, float(bits=4602678819172646912))" -/
#guard_msgs in #eval pyRun "case_default_by_keyword"

-- CPython: [0, 1]
/-- info: "[0, 1]" -/
#guard_msgs in #eval pyRun "case_mutable_default_supplied"

-- CPython: [1]
/-- info: "hole param:default-nonliteral" -/
#guard_msgs in #eval pyRun "case_mutable_default_needed"

-- CPython: (1, 2)
/-- info: "(1, 2)" -/
#guard_msgs in #eval pyRun "case_global_default_supplied"

-- CPython: (1, 4)
/-- info: "hole param:default-nonliteral" -/
#guard_msgs in #eval pyRun "case_global_default_needed"

-- CPython: 3
/-- info: "3" -/
#guard_msgs in #eval pyRun "case_lambda_default"

-- CPython: (1, None, False)
/-- info: "(1, None, False)" -/
#guard_msgs in #eval pyRun "case_method_default"

-- CPython: (1, 2, True)
/-- info: "(1, 2, True)" -/
#guard_msgs in #eval pyRun "case_method_default_kwonly"

-- CPython: (0, 1)
/-- info: "(0, 1)" -/
#guard_msgs in #eval pyRun "case_underscored_default"

-- CPython: (1, 2, 3)
/-- info: "(1, 2, 3)" -/
#guard_msgs in #eval pyRun "case_kwonly"

-- CPython: raise TypeError
/-- info: "raise TypeError" -/
#guard_msgs in #eval pyRun "case_kwonly_positional_rejected"

-- CPython: ((1, 2), None, {})
/-- info: "((1, 2), None, {})" -/
#guard_msgs in #eval pyRun "case_kw_after_varargs"

-- CPython: ((1,), 5, {'z': 6})
/-- info: "((1,), 5, {'z': 6})" -/
#guard_msgs in #eval pyRun "case_kw_after_varargs_named"

-- CPython: (1, 2, 3)
/-- info: "(1, 2, 3)" -/
#guard_msgs in #eval pyRun "case_posonly"

-- CPython: raise TypeError
/-- info: "raise TypeError" -/
#guard_msgs in #eval pyRun "case_posonly_keyword_rejected"

-- CPython: (1, {'a': 2})
/-- info: "(1, {'a': 2})" -/
#guard_msgs in #eval pyRun "case_posonly_name_goes_to_kwargs"

-- CPython: (2, 3)
/-- info: "(2, 3)" -/
#guard_msgs in #eval pyRun "case_nonlocal_counter"

-- CPython: 16
/-- info: "16" -/
#guard_msgs in #eval pyRun "case_nonlocal_shared_between_closures"

-- CPython: (10, 10)
/-- info: "(10, 10)" -/
#guard_msgs in #eval pyRun "case_nonlocal_through_two_levels"

-- CPython: 6
/-- info: "6" -/
#guard_msgs in #eval pyRun "case_nonlocal_in_a_loop"

-- CPython: (1, [2, 3])
/-- info: "(1, [2, 3])" -/
#guard_msgs in #eval pyRun "case_star_tail_of_tuple_is_a_list"

-- CPython: (1, [])
/-- info: "(1, [])" -/
#guard_msgs in #eval pyRun "case_star_tail_empty"

-- CPython: ('a', ['b', 'c'], 'd')
/-- info: "('a', ['b', 'c'], 'd')" -/
#guard_msgs in #eval pyRun "case_star_middle_of_str"

-- CPython: raise ValueError
/-- info: "raise ValueError" -/
#guard_msgs in #eval pyRun "case_star_too_short"

-- CPython: (['x', 'y'], 'z')
/-- info: "(['x', 'y'], 'z')" -/
#guard_msgs in #eval pyRun "case_star_head_of_str"

-- CPython: raise TypeError
/-- info: "raise TypeError" -/
#guard_msgs in #eval pyRun "case_star_noniterable"

end PyScoping
end Autoform.Core
