import Autoform.Lang.Core.Semantics
import Autoform.Generated.Cachetools

/-!
# Classes with a builtin base type — the `_HashedTuple` gap, closed

STRATEGY.md §31/§33/§34 record one confirmed **behavioural** divergence from CPython:
`class _HashedTuple(tuple)` in `cachetools/keys.py` translated to an ordinary class, so
`Expr.alloc` produced an opaque `Val.ref` and `Val.beq` could never equate the result of
`hashkey` with a tuple. Since `hashkey` is what `cachetools` uses to build cache keys, a
stored key and a computed key could not match.

Measured against **CPython 3.9.6**, running the upstream `_HashedTuple`/`hashkey` source:

```
>>> hashkey(0)                     (0,)      # type _HashedTuple
>>> hashkey((0,))                  ((0,),)   # type _HashedTuple
>>> hashkey(0) == (0,)             True
>>> hashkey(0) == ((0,),)          False
>>> hashkey(0) == (1,)             False
>>> isinstance(hashkey(0), tuple)  True
>>> {(0,): 'x'}[hashkey(0)]        'x'
```

Core's `hashkey` takes the packed varargs tuple `args` as its first parameter, so the Lean
call `hashkey (tuple [int 0])` is CPython's `hashkey(0)`, and
`hashkey (tuple [tuple [int 0]])` is CPython's `hashkey((0,))`.

## What is a proof here, and what is a test

Facts about `Val.beq`, `Val.truthy`, `valIn` and small `evalExpr` terms are **theorems**,
closed by `decide`/`rfl` in the kernel. `#print axioms` at the bottom shows they stand on
nothing but `propext`/`Quot.sound`/`Classical.choice`.

Facts that run a whole program, or that go through `Ctx.resolve`/`Ctx.classDefines`, are
**`#guard`s**. They are not provable by `decide` here: `String.endsWith` and
`Ctx.resolve`'s inner `go` do not reduce in the kernel. `#guard` is a build-time
assertion — it fails the build when it is false — and it introduces **no axiom**, unlike
`native_decide`, which would add `Lean.ofReduceBool` and be rejected by
`scripts/audit_all.py`.

## Non-vacuity

A representation that made everything compare equal would be worse than the opaque
reference it replaces, so §2 pins the **disagreements** as hard as the agreements, and §4
pins what is still excluded. Every expectation carries the CPython expression that
produced it.
-/

namespace Autoform.Core.BuiltinBaseTest

open Autoform.Core

/-! ## 1. The decisive test: `hashkey` -/

/-- The committed `cachetools` program, told that `_HashedTuple` inherits from `tuple`.

This is the one fact the CPG exporter must supply: `cartographer/export_ast.sc` now emits
it as `classBases` on the module initializer, and `render_lean.py` turns that into
`Program.builtinBases`. It is stated here rather than read out of
`Autoform/Generated/Cachetools.lean` because that module is **already stale** against
`ast-Cachetools.json` — 238 functions against 208, STRATEGY.md §34's standing hazard —
so re-rendering it is a separate change that also deletes declarations
`Autoform/SpecsGen/Cachetools.lean` depends on. `scripts/check_render.py` reports that
staleness today and still does; this file touches neither artifact. -/
def cachetoolsWithBases : Program :=
  { Autoform.Generated.program with builtinBases := [("_HashedTuple", .tuple)] }

/-- The same program with `builtinBases` empty — exactly what STRATEGY.md §34 measured. -/
def cachetoolsBefore : Program := Autoform.Generated.program

/-- `hashkey` applied to a varargs tuple, then compared with a plain `Val`. -/
private def hashkeyEq (p : Program) (args res : Val) : Bool :=
  match runFunc p 200 "hashkey" [args] with
  | .val v => Val.beq v res
  | _      => false

/-- Is the result of `hashkey` an opaque heap reference — the pre-change behaviour? -/
private def hashkeyIsRef (p : Program) (args : Val) : Bool :=
  match runFunc p 200 "hashkey" [args] with
  | .val (.ref _) => true
  | _             => false

/-- Does `hashkey`'s result find `expect` stored under a plain-tuple key? -/
private def hashkeyFinds (p : Program) (args : Val) (d : List (Val × Val))
    (expect : Val) : Bool :=
  match runFunc p 200 "hashkey" [args] with
  | .val v => match Stdlib.dictGet d v with
              | some w => Val.beq w expect
              | none   => false
  | _      => false

-- BEFORE: `EResult.val (Val.ref 0)`, an opaque reference, where CPython says `(0,)`.
#eval runFunc cachetoolsBefore 200 "hashkey" [.tuple [.int 0]]

-- AFTER: `EResult.val (Val.bobj "_HashedTuple" (Val.tuple [Val.int 0]))` — CPython's
-- `hashkey(0)`, which is `(0,)` of type `_HashedTuple`.
#eval runFunc cachetoolsWithBases 200 "hashkey" [.tuple [.int 0]]

-- The divergence, pinned: before the change the answer really was an opaque reference,
-- so nothing below is measuring something that already worked.
#guard hashkeyIsRef cachetoolsBefore (.tuple [.int 0]) = true
#guard hashkeyIsRef cachetoolsWithBases (.tuple [.int 0]) = false

-- **THE PASS/FAIL CRITERION.** CPython: `hashkey(0) == (0,)` is `True`.
#guard hashkeyEq cachetoolsWithBases (.tuple [.int 0]) (.tuple [.int 0]) = true

-- ...and it was `false` before the change. This is the defect, and its repair.
#guard hashkeyEq cachetoolsBefore (.tuple [.int 0]) (.tuple [.int 0]) = false

-- CPython: `hashkey((0,))` is `((0,),)`.
#guard hashkeyEq cachetoolsWithBases (.tuple [.tuple [.int 0]]) (.tuple [.tuple [.int 0]])
         = true

-- NON-VACUITY. CPython: `hashkey(0) == ((0,),)` is `False` — two keys that must not
-- collide do not.
#guard hashkeyEq cachetoolsWithBases (.tuple [.int 0]) (.tuple [.tuple [.int 0]]) = false

-- CPython: `hashkey(0) == (1,)` is `False`.
#guard hashkeyEq cachetoolsWithBases (.tuple [.int 0]) (.tuple [.int 1]) = false

-- CPython: `hashkey(0) == [0]` is `False` — not merely "contents equal".
#guard hashkeyEq cachetoolsWithBases (.tuple [.int 0]) (.list [.int 0]) = false

-- The cache-key round trip that motivated all of this: a key **stored** as a plain tuple
-- is **found** by a key computed through `hashkey`. CPython: `{(0,): 'x'}[hashkey(0)]`
-- is `'x'`. Before the change the lookup missed.
#guard hashkeyFinds cachetoolsWithBases (.tuple [.int 0])
         [(.tuple [.int 0], .str "x")] (.str "x") = true
#guard hashkeyFinds cachetoolsBefore (.tuple [.int 0])
         [(.tuple [.int 0], .str "x")] (.str "x") = false

-- ...and a *different* key is still not found, so the lookup is not matching everything.
#guard hashkeyFinds cachetoolsWithBases (.tuple [.int 0])
         [(.tuple [.int 1], .str "x")] (.str "x") = false

/-! ## 2. Non-vacuity, end to end

`A(tuple)`, `B(tuple)`, `L(list)`, `S(str)`, `D(dict)` and an ordinary `P`, each with no
body, so that `Expr.alloc` is the only thing under test. -/

/-- The fixture program. -/
def demo : Program :=
  { dialect := .python
  , builtinBases := [("A", .tuple), ("B", .tuple), ("L", .list), ("S", .str),
                     ("D", .dict)]
  , funcs :=
    [ { name := "m.py:<module>.mkA", params := ["x"], body := .ret (.alloc "A" [.name "x"]) }
    , { name := "m.py:<module>.mkB", params := ["x"], body := .ret (.alloc "B" [.name "x"]) }
    , { name := "m.py:<module>.mkL", params := ["x"], body := .ret (.alloc "L" [.name "x"]) }
    , { name := "m.py:<module>.mkS", params := ["x"], body := .ret (.alloc "S" [.name "x"]) }
    , { name := "m.py:<module>.mkD", params := ["x"], body := .ret (.alloc "D" [.name "x"]) }
      -- `A()`, the no-argument constructor.
    , { name := "m.py:<module>.mkA0", params := [], body := .ret (.alloc "A" []) }
      -- `P() == P()`: two *distinct* instances of an ordinary class.
    , { name := "m.py:<module>.eqPQ", params := [],
        body := .seq (.assign "p" (.alloc "P" []))
                (.seq (.assign "q" (.alloc "P" []))
                      (.ret (.binop "==" (.name "p") (.name "q")))) }
      -- `p == p`: one instance, compared with itself.
    , { name := "m.py:<module>.eqPP", params := [],
        body := .seq (.assign "p" (.alloc "P" []))
                     (.ret (.binop "==" (.name "p") (.name "p"))) }
    ] }

private def rn (p : Program) (f : String) (as : List Val) : EResult := runFunc p 100 f as

/-- Compare two entry-point results with `Val.beq`. -/
private def eqRun (f g : String) (a b : List Val) : Bool :=
  match rn demo f a, rn demo g b with
  | .val x, .val y => Val.beq x y
  | _,      _      => false

/-- Compare an entry-point result with a literal value. -/
private def eqVal (f : String) (a : List Val) (y : Val) : Bool :=
  match rn demo f a with
  | .val x => Val.beq x y
  | _      => false

/-- Did the entry point return `true`? -/
private def isTrue (r : EResult) : Bool :=
  match r with | .val (.bool b) => b | _ => false

/-- Did the entry point return an opaque heap reference? -/
private def isRef (r : EResult) : Bool :=
  match r with | .val (.ref _) => true | _ => false

/-! ### Equal where CPython is equal -/

-- CPython: `A((0,)) == (0,)` is `True`.
#guard eqVal "mkA" [.tuple [.int 0]] (.tuple [.int 0]) = true

-- CPython: `A((0,)) == B((0,))` is `True` — `tuple.__eq__` ignores the class, so two
-- *different* subclasses of `tuple` with equal contents are equal.
#guard eqRun "mkA" "mkB" [.tuple [.int 0]] [.tuple [.int 0]] = true

-- CPython: `L([1,2]) == [1,2]` is `True`.
#guard eqVal "mkL" [.list [.int 1, .int 2]] (.list [.int 1, .int 2]) = true

-- CPython: `S('ab') == 'ab'` is `True`.
#guard eqVal "mkS" [.str "ab"] (.str "ab") = true

-- CPython: `D({1:2}) == {1:2}` is `True`.
#guard eqVal "mkD" [.dict [(.int 1, .int 2)]] (.dict [(.int 1, .int 2)]) = true

-- CPython: `A() == ()` is `True` — the no-argument constructor.
#guard eqVal "mkA0" [] (.tuple []) = true

/-! ### **Not** equal where CPython is not equal — the non-vacuity half -/

-- CPython: `A((0,)) == A((1,))` is `False`.
#guard eqRun "mkA" "mkA" [.tuple [.int 0]] [.tuple [.int 1]] = false

-- CPython: `A((0,)) == (1,)` is `False`.
#guard eqVal "mkA" [.tuple [.int 0]] (.tuple [.int 1]) = false

-- CPython: `A((0,)) == [0]` is `False` — a `tuple` subclass is not a list, even with
-- identical contents.
#guard eqVal "mkA" [.tuple [.int 0]] (.list [.int 0]) = false

-- CPython: `A((0,)) == 0` is `False`.
#guard eqVal "mkA" [.tuple [.int 0]] (.int 0) = false

-- CPython: `A() == (0,)` is `False` — the empty instance is not a universal equal.
#guard eqVal "mkA0" [] (.tuple [.int 0]) = false

-- CPython: `L([1,2]) == (1,2)` is `False` — a `list` subclass is not a tuple.
#guard eqVal "mkL" [.list [.int 1, .int 2]] (.tuple [.int 1, .int 2]) = false

-- CPython: `S('ab') == 'ac'` is `False`.
#guard eqVal "mkS" [.str "ab"] (.str "ac") = false

/-! ### Ordinary classes are untouched: still reference identity

This is the property a representation that compared every object structurally would have
destroyed, and it is why the `bobj` payload is *opt-in* per class. -/

-- CPython: `P() == P()` is `False` for `class P: pass` — two distinct instances.
#guard isTrue (rn demo "eqPQ" []) = false

-- CPython: `p == p` is `True` — the same instance.
#guard isTrue (rn demo "eqPP" []) = true

-- A class the exporter recorded no base for is still an opaque `Val.ref`: dropping
-- `builtinBases` restores the pre-change behaviour exactly, for every existing corpus.
#guard isRef (rn { demo with builtinBases := [] } "mkA" [.tuple [.int 0]]) = true
#guard isRef (rn demo "mkA" [.tuple [.int 0]]) = false

/-! ## 3. The value-level facts, as kernel proofs

Everything above runs a program. Everything here is a theorem about the primitives those
programs depend on. -/

/-- CPython: `A((0,)) == (0,)` and `(0,) == A((0,))` are both `True`; equality is
symmetric across the wrapper. -/
theorem beq_bobj_tuple :
    (Val.beq (.bobj "A" (.tuple [.int 0])) (.tuple [.int 0]) = true)
    ∧ (Val.beq (.tuple [.int 0]) (.bobj "A" (.tuple [.int 0])) = true) := by decide

/-- CPython: `A((0,)) == B((0,))` is `True`. -/
theorem beq_bobj_bobj_cross_class :
    Val.beq (.bobj "A" (.tuple [.int 0])) (.bobj "B" (.tuple [.int 0])) = true := by decide

/-- CPython: `A((0,)) == A((1,))` is `False`. -/
theorem beq_bobj_differs :
    Val.beq (.bobj "A" (.tuple [.int 0])) (.bobj "A" (.tuple [.int 1])) = false := by decide

/-- CPython: `A((0,)) == [0]` is `False`; a `tuple` subclass is not a list. -/
theorem beq_bobj_wrong_base :
    Val.beq (.bobj "A" (.tuple [.int 0])) (.list [.int 0]) = false := by decide

/-- CPython: `A((0,)) == 0` is `False`. -/
theorem beq_bobj_scalar :
    Val.beq (.bobj "A" (.tuple [.int 0])) (.int 0) = false := by decide

/-- A `bobj` is never equal to an object reference, in either direction — which is what
keeps ordinary classes on reference identity. -/
theorem beq_bobj_ref :
    (Val.beq (.bobj "A" (.tuple [])) (.ref 0) = false)
    ∧ (Val.beq (.ref 0) (.bobj "A" (.tuple [])) = false) := by decide

/-- Two distinct references are unequal; the same reference is equal to itself. This is
the pre-existing behaviour for ordinary classes, unchanged. -/
theorem beq_ref_identity :
    (Val.beq (.ref 0) (.ref 1) = false) ∧ (Val.beq (.ref 0) (.ref 0) = true) := by decide

/-- CPython: `bool(A(()))` is `False`, `bool(A((0,)))` is `True`. -/
theorem truthy_bobj :
    (Val.truthy (.bobj "A" (.tuple [])) = false)
    ∧ (Val.truthy (.bobj "A" (.tuple [.int 0])) = true) := by decide

/-- CPython: `bool(S(''))` is `False`, `bool(S('a'))` is `True`. -/
theorem truthy_bobj_str :
    (Val.truthy (.bobj "S" (.str "")) = false)
    ∧ (Val.truthy (.bobj "S" (.str "a")) = true) := by decide

/-- CPython: `0 in A((0,))` is `True`. -/
theorem valIn_bobj_true :
    valIn (.int 0) (.bobj "A" (.tuple [.int 0])) = .val (.bool true) := by rfl

/-- CPython: `1 in A((0,))` is `False`. -/
theorem valIn_bobj_false :
    valIn (.int 1) (.bobj "A" (.tuple [.int 0])) = .val (.bool false) := by rfl

/-- CPython: `A((7,))[0]` is `7`; indexing sees through the base. -/
theorem index_bobj :
    evalExpr { dialect := .python, table := [] } 5 [] [("a", .bobj "A" (.tuple [.int 7]))]
      (.index (.name "a") (.lit (.int 0))) = ([], .val (.int 7)) := by rfl

/-- CPython: `for x in A((7,))` iterates `7`. -/
theorem iterable_bobj :
    Val.iterable (.bobj "A" (.tuple [.int 7])) = some [.int 7] := by rfl

/-- CPython: `isinstance(A((0,)), tuple)` is `True`, `isinstance(A((0,)), list)` is
`False`. -/
theorem isInstance_bobj :
    (Stdlib.isInstance (.bobj "A" (.tuple [.int 0])) "tuple" = some true)
    ∧ (Stdlib.isInstance (.bobj "A" (.tuple [.int 0])) "list" = some false) := by decide

/-- `isinstance(x, A)` — a *user* class name — stays undecidable, i.e. `none`, which the
caller turns into a hole. Answering `False` would be a silent wrong answer. -/
theorem isInstance_own_class_is_a_hole :
    Stdlib.isInstance (.bobj "A" (.tuple [.int 0])) "A" = none := by decide

/-! ## 4. What is excluded, each with a test showing it **holes**

None of these is a wrong answer. Every one is counted ignorance the ledger can see. -/

/-- The hole label an `EResult` carries, or `""`. -/
private def holeOf : EResult → String
  | .hole l => l
  | _       => ""

/-- **No instance attributes.** A builtin-based instance is a value, not a heap object, so
it has nowhere to put a field. `_HashedTuple.__hash__`'s memo field is exactly this case:
CPython answers `None`, Core holes. -/
theorem excluded_field_access :
    evalExpr { dialect := .python, table := [] } 5 [] [("a", .bobj "A" (.tuple []))]
      (.field (.name "a") "memo") = ([], .hole "field:memo:non-object") := by rfl

/-- **Arithmetic on a builtin-based instance is a hole.** CPython dispatches
`_HashedTuple.__add__`; Core's `applyBinop` cannot dispatch a dunder for *any* class, so
`+` on a `bobj` is left exactly where `+` on a `Val.ref` already was. Unwrapping it to a
plain tuple would silently change the *type* of `typedkey`'s result. -/
theorem excluded_add :
    applyBinop .python "+" (.bobj "A" (.tuple [.int 0])) (.tuple [.int 1])
      = .hole "binop:+" := by rfl

-- **A class with its own `__init__` is refused**, not approximated: Core would have to
-- run it against a value that has nowhere to write.
#guard holeOf (allocBuiltin
    { dialect := .python,
      table := [("m.py:<module>.A.__init__",
                 { name := "m.py:<module>.A.__init__", params := [], body := .skip })] }
    "A" .tuple []) = "alloc:builtin-base:A:own-__init__"

-- **A class that overrides `__eq__` is refused too.** `Val.beq` has no dunder dispatch,
-- so honouring the class would mean silently ignoring the override — the exact failure
-- mode this representation exists to avoid.
#guard holeOf (allocBuiltin
    { dialect := .python,
      table := [("m.py:<module>.A.__eq__",
                 { name := "m.py:<module>.A.__eq__", params := [], body := .skip })] }
    "A" .tuple []) = "alloc:builtin-base:A:own-__eq__"

-- ...and a class with neither is accepted, so the two guards above are not vacuous.
#guard holeOf (allocBuiltin { dialect := .python, table := [] } "A" .tuple []) = ""

-- `str(x)` for a non-string needs `repr`, which Core does not model.
#guard holeOf (allocBuiltin { dialect := .python, table := [] } "S" .str [.int 3])
         = "alloc:builtin-base:S:str-of-non-str"

-- `dict(pairs)` likewise.
#guard holeOf (allocBuiltin { dialect := .python, table := [] } "D" .dict [.list []])
         = "alloc:builtin-base:D:dict-from-non-dict"

-- `tuple(3)` is a `TypeError` in CPython. Core holes rather than raising, because `alloc`
-- cannot know which exception a class it only partly understands would raise.
#guard holeOf (allocBuiltin { dialect := .python, table := [] } "A" .tuple [.int 3])
         = "alloc:builtin-base:A:non-iterable"

-- More than one constructor argument is out of scope.
#guard holeOf (allocBuiltin { dialect := .python, table := [] } "A" .tuple
                 [.tuple [], .tuple []]) = "alloc:builtin-base:A:multiple-args"

/-- **`len` of a builtin-based instance is a hole**, and it is the one arbitrary exclusion
here: adding the case to `Stdlib.builtinCore` defeats the branch enumeration in
`Stdlib.builtin_heap_unchanged` (a `whnf` timeout that raising the heartbeat budget does
not fix). CPython: `len(A((0,)))` is `1`. -/
theorem excluded_len :
    Stdlib.builtin .python [] "len" [.bobj "A" (.tuple [.int 0])] = none := by rfl

/-- `list`, `tuple`, `sorted`, `sum`, `min` and `max` all reach the base through
`Stdlib.elems`, so this is a single named gap and not a class of them. CPython:
`tuple(A((0,)))` is `(0,)`. -/
theorem included_tuple_of_bobj :
    Stdlib.builtin .python [] "tuple" [.bobj "A" (.tuple [.int 0])]
      = some ([], .val (.tuple [.int 0])) := by rfl

/-! ### Bases that are out of reach entirely

* **`class X(Exception)`.** Core represents an exception as the bare `Val.str` naming its
  class (`Stdlib.excNames`, `numToE`), so an exception subclass has nowhere to put a
  payload and no hierarchy to be caught by. `BuiltinBase` deliberately has no constructor
  for it, so such a class stays an ordinary class and its instances stay opaque
  references — unchanged, and never silently equated with anything.
* **Multiple inheritance**, and a builtin base reached *transitively* (`class Y(X)` where
  `class X(tuple)`). `Program.builtinBases` records one base for one class, and
  `export_ast.sc` records nothing for a class with more than one base, so those stay
  opaque references.
* **`__slots__`, `__new__`, metaclasses.** Not modelled anywhere in Core.
* **`int`, `float`, `set`, `frozenset` bases.** `int`/`float` would need the numeric tower
  to accept a wrapper; `set`/`frozenset` have no `Val` at all (`Stdlib`'s module docstring
  records why).
* **Mutation** of a `list`/`dict` base, exactly as for Core's own containers:
  `Stmt.setIndex` is `setIndex:immutable-containers` and a mutating container method is
  `mcall:<m>:unboxed-container`. See `docs/boxed-containers.md`.
-/

/-! ## 5. Axioms -/

#print axioms beq_bobj_tuple
#print axioms beq_bobj_bobj_cross_class
#print axioms beq_bobj_differs
#print axioms beq_bobj_wrong_base
#print axioms beq_bobj_ref
#print axioms beq_ref_identity
#print axioms truthy_bobj
#print axioms valIn_bobj_true
#print axioms valIn_bobj_false
#print axioms index_bobj
#print axioms iterable_bobj
#print axioms isInstance_bobj
#print axioms isInstance_own_class_is_a_hole
#print axioms excluded_field_access
#print axioms excluded_add
#print axioms excluded_len
#print axioms included_tuple_of_bobj

end Autoform.Core.BuiltinBaseTest
