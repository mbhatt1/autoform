import Autoform.Lang.Core.Semantics

/-!
# The calling convention, checked against CPython

`Expr.starred` / `Expr.kwargE` / `Expr.dstarred` and `Func.vararg` / `Func.kwarg` closed
`op:starredUnpack`, which was the largest hole category on `cachetools` (36 of 78). A
construct that closes a hole category by *always* holing, or by always returning `unit`,
would make every theorem about it pass and mean nothing — the §17/§30 failure shape this
project keeps catching. So this file is the anti-vacuity evidence.

Every `#eval` below is paired with the value **CPython actually printed**, recorded in the
comment beside it. The source of those values is:

```python
def f(a, b):        return (a, b)
def g(*a):          return a
def h(a, *rest):    return (a, rest)
def k(a=None, **kw):return (a, kw)
def m(*a, **kw):    return (a, kw)
```

run under CPython 3.9.6. The five `Func`s below are those definitions written directly in
`Core`, and the callers are the call expressions.

Two modelling notes, stated rather than glossed:

* **Core has no default values.** CPython's `def k(a=None, ...)` binds `a` to `None` when
  no argument supplies it; Core leaves `a` unbound, and an unbound read is `Val.unit`.
  `unit` is the closest thing Core has to `None`, so `k(**{'z': 9})` is compared against
  `(None, {'z': 9})` with `None` read as `unit`. Defaults remain unmodelled.
* **Surplus positional arguments now raise, as CPython does.** `f(1, 2, 3)` on
  `def f(a, b)` used to truncate to `(1, 2)`; `posRejected` makes it a `TypeError`. What
  is still accepted where CPython raises is an *under*-supplied call, because Core does
  not model default values and cannot tell a missing argument from a defaulted one. See
  `surplusPositional_now_agrees_with_cpython`.
-/

namespace Autoform.Core
namespace CallingConvention

/-- `def f(a, b): return (a, b)` -/
def f_f : Func :=
  { name := "f", params := ["a", "b"]
  , body := .ret (.tupleE [.name "a", .name "b"]) }

/-- `def g(*a): return a` -/
def f_g : Func :=
  { name := "g", params := ["a"], vararg := some "a"
  , body := .ret (.name "a") }

/-- `def h(a, *rest): return (a, rest)` -/
def f_h : Func :=
  { name := "h", params := ["a", "rest"], vararg := some "rest"
  , body := .ret (.tupleE [.name "a", .name "rest"]) }

/-- `def k(a=None, **kw): return (a, kw)` — without the default. -/
def f_k : Func :=
  { name := "k", params := ["a", "kw"], kwarg := some "kw"
  , body := .ret (.tupleE [.name "a", .name "kw"]) }

/-- `def m(*a, **kw): return (a, kw)` -/
def f_m : Func :=
  { name := "m", params := ["a", "kw"], vararg := some "a", kwarg := some "kw"
  , body := .ret (.tupleE [.name "a", .name "kw"]) }

/-- One caller per case: a zero-argument function whose body is the call expression. -/
def caller (nm : String) (e : Expr) : Func := { name := nm, params := [], body := .ret e }

def prog : Program := { dialect := .python, funcs :=
  [ f_f, f_g, f_h, f_k, f_m
  , caller "c1"  (.call "f" [.starred (.listE [.lit (.int 1), .lit (.int 2)])])
  , caller "c2"  (.call "f" [.lit (.int 1), .starred (.listE [.lit (.int 2)])])
  , caller "c3"  (.call "g" [])
  , caller "c4"  (.call "g" [.lit (.int 1)])
  , caller "c5"  (.call "g" [.lit (.int 1), .lit (.int 2), .lit (.int 3)])
  , caller "c6"  (.call "g" [.starred (.listE [.lit (.int 1), .lit (.int 2), .lit (.int 3)])])
  , caller "c7"  (.call "h" [.lit (.int 1), .lit (.int 2), .lit (.int 3)])
  , caller "c8"  (.call "h" [.lit (.int 1)])
  , caller "c9"  (.call "h" [.starred (.listE [.lit (.int 1), .lit (.int 2), .lit (.int 3)])])
  , caller "c10" (.call "k" [.dstarred (.dictE [(.lit (.str "a"), .lit (.int 1))])])
  , caller "c11" (.call "k" [.dstarred (.dictE [(.lit (.str "z"), .lit (.int 9))])])
  , caller "c12" (.call "k" [.kwargE "a" (.lit (.int 5))])
  , caller "c13" (.call "m" [ .lit (.int 1)
                            , .starred (.listE [.lit (.int 2), .lit (.int 3)])
                            , .kwargE "x" (.lit (.int 4))
                            , .dstarred (.dictE [(.lit (.str "y"), .lit (.int 5))])])
  , caller "c14" (.call "g" [.starred (.tupleE [.lit (.int 4), .lit (.int 5)])])
  , caller "c15" (.call "g" [.starred (.dictE [ (.lit (.str "p"), .lit (.int 1))
                                              , (.lit (.str "q"), .lit (.int 2))])])
  , caller "e1"  (.call "f" [.starred (.lit (.int 1))])
  , caller "e2"  (.call "f" [.dstarred (.dictE [(.lit (.int 1), .lit (.int 2))])])
  , caller "e3"  (.call "f" [.dstarred (.listE [.lit (.int 1)])])
  , caller "e4"  (.call "f" [.lit (.int 1), .lit (.int 2), .kwargE "q" (.lit (.int 3))])
  , caller "s1"  (.starred (.listE [.lit (.int 1)]))
  , caller "d2"  (.call "h" [.lit (.int 1), .kwargE "a" (.lit (.int 2))])
  -- str iteration, now that `Val.iterable` has a `str` case.
  , caller "t1"  (.call "g" [.starred (.lit (.str "ab"))])
  , caller "t2"  (.call "g" [.starred (.lit (.str ""))])
  , { name := "t3", params := []
    , body := .seq (.forIn "c" (.lit (.str "abc")) (.assign "acc" (.name "c")))
                   (.ret (.name "acc")) }
  -- exact-arity and under-supplied calls, which must keep succeeding now that surplus
  -- ones raise.
  , caller "p1"  (.call "f" [.lit (.int 1), .lit (.int 2)])
  , caller "p2"  (.call "f" [.lit (.int 1)])
  ] }

/-- `prog` plus the surplus-positional caller, which is kept in its own program only
because it was added later. -/
def prog' : Program := { prog with funcs := prog.funcs ++
  [ caller "x1" (.call "f" [.lit (.int 1), .lit (.int 2), .lit (.int 3)]) ] }

def run (nm : String) : String :=
  reprStr (runFunc (if nm == "x1" then prog' else prog) 60 nm [])

/-- `run` with the namespace prefix stripped, so a pinned expectation reads the way the
comments beside the `#eval`s do. Purely cosmetic: it is `String.replace`, not a
reinterpretation of the result. -/
def pin (nm : String) : String := (run nm).replace "Autoform.Core." ""

/-! ## Splicing into a fixed parameter list -/

-- CPython: f(*[1,2])   ==  (1, 2)
#eval run "c1"   -- val (tuple [int 1, int 2])
-- CPython: f(1, *[2])  ==  (1, 2)
#eval run "c2"   -- val (tuple [int 1, int 2])

/-! ## A `*args` parameter, receiving 0, 1 and 3 arguments

The zero case is the one that distinguishes a real vararg from a hole or a `unit`: CPython
binds the **empty tuple**, not `None`. -/

-- CPython: g()          ==  ()
#eval run "c3"   -- val (tuple [])
-- CPython: g(1)         ==  (1,)
#eval run "c4"   -- val (tuple [int 1])
-- CPython: g(1,2,3)     ==  (1, 2, 3)
#eval run "c5"   -- val (tuple [int 1, int 2, int 3])
-- CPython: g(*[1,2,3])  ==  (1, 2, 3)
#eval run "c6"   -- val (tuple [int 1, int 2, int 3])

/-! ## The interaction with a positional parameter

`def h(a, *rest)` must give `a` the first argument and `rest` the remainder — including
when the remainder is empty. -/

-- CPython: h(1,2,3)     ==  (1, (2, 3))
#eval run "c7"   -- val (tuple [int 1, tuple [int 2, int 3]])
-- CPython: h(1)         ==  (1, ())
#eval run "c8"   -- val (tuple [int 1, tuple []])
-- CPython: h(*[1,2,3])  ==  (1, (2, 3))
#eval run "c9"   -- val (tuple [int 1, tuple [int 2, int 3]])

/-! ## Keyword arguments

A `**` splice whose key names a positional parameter binds that parameter; one that does
not lands in `**kw`. -/

-- CPython: k(**{'a':1}) ==  (1, {})
#eval run "c10"  -- val (tuple [int 1, dict []])
-- CPython: k(**{'z':9}) ==  (None, {'z': 9})   -- `None` is modelled as `unit`
#eval run "c11"  -- val (tuple [unit, dict [(str "z", int 9)]])
-- CPython: k(a=5)       ==  (5, {})
#eval run "c12"  -- val (tuple [int 5, dict []])

/-! ## All four forms in one call, and iterating a tuple and a dict -/

-- CPython: m(1, *[2,3], x=4, **{'y':5}) == ((1, 2, 3), {'x': 4, 'y': 5})
#eval run "c13"  -- val (tuple [tuple [1,2,3], dict [("x",4), ("y",5)]])
-- CPython: g(*(4,5))    ==  (4, 5)
#eval run "c14"  -- val (tuple [int 4, int 5])
-- CPython: g(*{'p':1,'q':2}) == ('p', 'q')     -- `*` on a dict iterates its keys
#eval run "c15"  -- val (tuple [str "p", str "q"])

/-! ## The error cases

CPython raises `TypeError` for each of these, and so does Core. They are *exceptions*, not
holes: the behaviour is modelled, not skipped. -/

-- CPython: f(*1)        ==  TypeError: argument after * must be an iterable, not int
#eval run "e1"   -- exn (str "TypeError")
-- CPython: f(**{1:2})   ==  TypeError: keywords must be strings
#eval run "e2"   -- exn (str "TypeError")
-- CPython: f(**[1])     ==  TypeError: argument after ** must be a mapping, not list
#eval run "e3"   -- exn (str "TypeError")
-- CPython: f(1,2,q=3)   ==  TypeError: f() got an unexpected keyword argument 'q'
#eval run "e4"   -- exn (str "TypeError")

/-! ## And the one place the forms are *not* meaningful

A starred form outside an argument list has no value. It is a hole with its own label, not
a silently invented value — which is the whole point of keeping these as argument forms
rather than as expressions. -/

-- No CPython counterpart: `x = *[1]` is a SyntaxError.
#eval run "s1"   -- hole "op:starred-outside-call"

/-! ## The same facts as theorems

`#eval`s are evidence a reader can check; these are checked by the kernel. -/

theorem starred_splices_into_fixed_params :
    runFunc prog 60 "c1" [] = .val (.tuple [.int 1, .int 2]) := by rfl

theorem vararg_of_zero_args_is_the_empty_tuple :
    runFunc prog 60 "c3" [] = .val (.tuple []) := by rfl

theorem vararg_after_a_positional_param :
    runFunc prog 60 "c7" [] = .val (.tuple [.int 1, .tuple [.int 2, .int 3]]) := by rfl

theorem doubleStar_binds_a_named_param :
    runFunc prog 60 "c10" [] = .val (.tuple [.int 1, .dict []]) := by rfl

set_option maxRecDepth 100000 in
theorem doubleStar_overflow_lands_in_kwargs :
    runFunc prog 60 "c11" [] = .val (.tuple [.unit, .dict [(.str "z", .int 9)]]) := by
  simp +decide [runFunc, prog, caller, f_f, f_g, f_h, f_k, f_m, Program.table, Heap.get,
    Ctx.resolve, Ctx.resolve.go, String.endsWith, applyFunc, bindParams, Func.posParams,
    kwargsRejected, execStmt, evalExpr, evalList, evalPairs, strKeyed, Env.set, Env.get]

theorem all_four_forms_together :
    runFunc prog 60 "c13" []
      = .val (.tuple [ .tuple [.int 1, .int 2, .int 3]
                     , .dict [(.str "x", .int 4), (.str "y", .int 5)] ]) := by rfl

theorem starred_noniterable_raises :
    runFunc prog 60 "e1" [] = .exn (.str "TypeError") := by rfl

theorem unexpected_keyword_raises :
    runFunc prog 60 "e4" [] = .exn (.str "TypeError") := by rfl

theorem starred_outside_a_call_is_a_hole :
    runFunc prog 60 "s1" [] = .hole "op:starred-outside-call" := by rfl

/-! ## Two divergences closed, and one still open

Both fixes are paired with the value CPython 3.9.6 actually printed, pinned with
`#guard_msgs` so the build fails if either regresses. `#guard_msgs` adds no axiom.

### `str` is iterable

`Val.iterable` had no `str` case, so `g(*"ab")` raised `TypeError` and `for c in "ab"`
holed. It now yields one-character strings, as CPython does. -/

-- CPython: g(*"ab") == ('a', 'b')
/-- info: "EResult.val (Val.tuple [Val.str \"a\", Val.str \"b\"])" -/
#guard_msgs in #eval pin "t1"

-- The boundary in the other direction. `t1` already rules out a `str` case that returns
-- `some []` for everything; this rules out one that returns `none` on the empty string,
-- which would raise where CPython yields the empty tuple.
-- CPython: g(*"") == ()
/-- info: "EResult.val (Val.tuple [])" -/
#guard_msgs in #eval pin "t2"

-- And the construct the gap actually broke in real code: `for c in "abc"`.
-- CPython: acc = None; for c in "abc": acc = c  ==> acc == 'c'
/-- info: "EResult.val (Val.str \"c\")" -/
#guard_msgs in #eval pin "t3"

theorem str_is_iterable :
    runFunc prog 60 "t1" [] = .val (.tuple [.str "a", .str "b"]) := by rfl

theorem str_iteration_is_not_empty :
    runFunc prog 60 "t3" [] = .val (.str "c") := by rfl

/-! ### Surplus positional arguments raise

`applyFunc` used to truncate: `f(1, 2, 3)` on `def f(a, b)` returned `(1, 2)`. CPython
raises. `posRejected` now makes Core raise too. Only a *surplus* is rejected — Core has no
default values, so an under-supplied call must still be accepted (`p2` below), and a
callee with `*args` absorbs any number of arguments (`c5`). Those two cases are the
anti-vacuity evidence: a check that fired on every call would make `p1`, `p2` and `c5`
raise as well, and all three are pinned to values, not exceptions. -/

-- CPython: f(1,2,3)    ==  TypeError: f() takes 2 positional arguments but 3 were given
/-- info: "EResult.exn (Val.str \"TypeError\")" -/
#guard_msgs in #eval pin "x1"
-- CPython: f(1,2)      ==  (1, 2)          — the exact-arity call still succeeds
/-- info: "EResult.val (Val.tuple [Val.int 1, Val.int 2])" -/
#guard_msgs in #eval pin "p1"
-- No exact CPython counterpart: `f(1)` is a TypeError there too, but for a *missing*
-- argument, which Core cannot distinguish from an unmodelled default. Left accepted,
-- deliberately; `unit` is the unbound read.
/-- info: "EResult.val (Val.tuple [Val.int 1, Val.unit])" -/
#guard_msgs in #eval pin "p2"
-- CPython: g(1,2,3)    ==  (1, 2, 3)       — `*args` absorbs the surplus, no raise
/-- info: "EResult.val\n  (Val.tuple [Val.int 1, Val.int 2, Val.int 3])" -/
#guard_msgs in #eval pin "c5"

/-- What used to be `surplusPositional_is_a_known_divergence`, now recording agreement. -/
theorem surplusPositional_now_agrees_with_cpython :
    runFunc prog' 60 "x1" [] = .exn (.str "TypeError") := by rfl

/-- The raise is not vacuous in the direction that matters: the exact-arity call it sits
next to still returns a value. -/
theorem exactArity_still_succeeds :
    runFunc prog 60 "p1" [] = .val (.tuple [.int 1, .int 2]) := by rfl

/-- Nor does it fire on a `*args` callee. -/
theorem vararg_absorbs_surplus :
    runFunc prog 60 "c5" [] = .val (.tuple [.int 1, .int 2, .int 3]) := by rfl

/-! ### Still open: duplicate arguments -/

-- CPython: h(1, a=2) == TypeError: h() got multiple values for argument 'a'
-- Core: the keyword binding shadows the positional one and the call succeeds.
#eval run "d2"   -- val (tuple [int 2, tuple []])   [DIVERGES from CPython]

theorem duplicate_argument_is_not_detected :
    runFunc prog 60 "d2" [] = .val (.tuple [.int 2, .tuple []]) := by rfl

end CallingConvention
end Autoform.Core
