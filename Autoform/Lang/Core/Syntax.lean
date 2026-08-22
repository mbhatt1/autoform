import Specimen
import Autoform.Lang.Core.Float

/-!
# Core — a universal deep-embedded imperative language

`Imp` proved the harness works. `Core` is the real target: it is deliberately shaped to
match **Joern's code property graph node vocabulary**, which already normalizes
C/C++/Java/JavaScript/Python/Kotlin/binaries into a single AST schema.

That is the trick for "arbitrary codebase". We do not write one transpiler per language;
we write one semantics for the CPG core and one CPG→Lean exporter, and every
Joern-supported front end comes along for free.

The price is honesty about coverage, which is why holes are first class:

* `Expr.hole` — an unmapped expression, tagged with the CPG node label that produced it.
* `Stmt.hole` — an unmapped statement, likewise.

Nothing is ever silently dropped. The ledger counts holes, and a program with holes
cannot be proved to do anything at the hole. That is the point, not a limitation.
-/

namespace Autoform.Core

/-- Source-language dialect.

**Two constructors are not enough** and this is known (STRATEGY.md §29): six languages
have been run through the pipeline and they disagree on integer width, string semantics,
boolean-operator semantics, and equality. `cLike` currently means "32-bit truncating C"
and is applied to Java, Go, JavaScript and TypeScript, which are none of those things.

The fix is a constructor per language. The prerequisite — done here — is that *every*
dialect-dependent decision is a named predicate below rather than a `match` scattered
through the interpreter, so adding `java`/`go`/`javascript` means extending this table
and nothing else. Every time this project added a dialect axis (integer division, unary
minus, strings, now booleans and widths) it under-provisioned it; centralizing the
decisions is what stops the next axis from touching 56 call sites. -/
inductive Dialect where
  | python
  | cLike
  deriving Repr, Inhabited, DecidableEq

namespace Dialect

/-- Do `and`/`or` evaluate to one of their **operands** (Python, JavaScript) rather than
to a boolean (C, Java, Go)? `0 and 5` is `0` in Python and `1` in C. -/
def boolOpsAreValues : Dialect → Bool
  | .python => true
  | .cLike  => false

/-- Are strings **values** with content equality and concatenation (Python, Java, Go,
JavaScript), or pointers with address semantics (C)? Under pointer semantics `+`, `<`,
`>` and `==` on strings are holes rather than the content operations. -/
def stringsAreValues : Dialect → Bool
  | .python => true
  | .cLike  => false

/-- Is `e.f` on a **dict** value a member selection?

A C aggregate initializer — `static struct crypto_alg alg = { .cra_name = "842", .
cra_priority = 100 }` — is a finite map from field names to values, which is exactly
`Val.dict` with string keys, and C struct assignment copies, so value semantics is the
right semantics for it. Under a C-family dialect `alg.cra_priority` therefore reads the
key `"cra_priority"` out of that map.

Under Python it must **not**: `{'a': 1}.a` is an `AttributeError`, not `1`, and answering
`1` would be a silent wrong answer of the §12 kind. So `.python` says `false` and the
access stays the `field:a:non-object` hole it has always been.

Note what this does *not* buy: a `dict` is not on the heap, so `e.f = v` on one is still
`setField:non-object`. A struct whose fields are written after initialization is a hole,
not a wrong answer. -/
def fieldsOnDicts : Dialect → Bool
  | .python => false
  | .cLike  => true

/-- Does comparing an integer against a float compare **exactly** (Python: `10**23 ==
1e23` is `False`), or promote the integer to a double first (C)? -/
def comparesIntFloatExactly : Dialect → Bool
  | .python => true
  | .cLike  => false

end Dialect

/-- Float configuration implied by a `Core.Dialect`. `cLike` gets `cDouble`, matching what
the oracle measures on x86-64 (SSE2, `FLT_EVAL_METHOD = 0`); switch it to
`FConfig.cDoubleExcess` to *surface* excess-precision dependence instead of assuming it
away. As with `NumConfig`, the ledger must record which one a result was obtained under —
`1.0 / 0.0` is `ZeroDivisionError` under one and `inf` under the other. -/
def Dialect.toFConfig : Dialect → FConfig
  | .python => FConfig.python
  | .cLike  => FConfig.cDouble

/-- A heap address. Objects are boxed and mutable; everything else is a value. -/
abbrev Ref := Nat

/-- Runtime values. A small universal core; anything richer becomes a hole. -/
inductive Val where
  | int   : Int → Val
  | str   : String → Val
  | bool  : Bool → Val
  /-- An IEEE 754 float, as a bit pattern plus its format (`Autoform/Lang/Core/Float.lean`).

  **`Val.beq` must not compare these structurally.** `Fl` derives `DecidableEq`, so
  `.float a == .float b` on the bit patterns is available and is *wrong* in both
  directions: NaN would equal itself and `-0.0` would differ from `+0.0`. Both are proved
  in `Float.lean` (`float_beq_is_not_bit_equality`, `float_bit_equality_is_not_beq`), and
  `Val.beq` below routes floats through `Fl.eqv` for exactly this reason. -/
  | float : Fl → Val
  | unit  : Val
  | list  : List Val → Val
  | tuple : List Val → Val
  /-- Association list, not a hash map: key order is observable and we do not want to
  silently impose one language's iteration order on another's. -/
  | dict  : List (Val × Val) → Val
  /-- A reference to a heap object. Reference identity is what `is` compares. -/
  | ref   : Ref → Val
  /-- A function or method used as a value (`METHOD_REF`), or a class (`TYPE_REF`). -/
  | fn    : String → Val
  /-- A class together with the bindings it captured, for classes defined inside a
  function whose methods read the enclosing scope. -/
  | clsClos : String → List (String × Val) → Val
  /-- A closure: a function together with the bindings it captured. Capture is **by
  value**, which is why `nonlocal` *writes* remain a hole — see `Semantics.lean`. -/
  | clos  : String → List (String × Val) → Val
  /-- An instance of a class whose base is a **builtin type**: `class X(tuple)`,
  `class X(list)`, `class X(dict)`, `class X(str)`. Carries the class name and the
  underlying builtin value.

  ## Why this shape, and not a payload on `Obj`

  The obvious cheaper alternative is `Obj.builtin : Option Val`, leaving the value a
  `Val.ref`. It does not work, and the reason is structural rather than a matter of
  taste: **`Val.beq`, `applyBinop`, `valIn` and `Val.truthy` do not take the heap.**
  They are pure functions of values, and they are exactly the functions that have to
  agree with the builtin. Making the `Obj` payload visible to them means threading a
  `Heap` through `Val.beq` — which is also the `BEq Val` instance, is used inside
  `Val.beqL`/`beqP`, inside `Stdlib`'s association-list helpers, and inside dozens of
  `Refine.lean` theorems. That is a far larger and more dangerous edit than adding a
  constructor, and it leaves `Val.beq` able to *fail* to consult the heap on any path —
  the silent-wrong failure mode this project keeps finding.

  So the payload lives in the value. There is exactly one copy of an instance's builtin
  state and no way for a value and a heap object to disagree about it.

  ## What this costs, stated plainly

  A `bobj` has **no mutable instance attributes**: it is not on the heap, so `e.f` on one
  is `field:f:non-object` and `e.f = v` is `setField:f:non-object` — holes, not wrong
  answers. `_HashedTuple.__hash__`'s memo field is therefore a hole. Classes with a
  builtin base that define `__init__` or `__eq__` are refused at construction
  (`alloc:builtin-base:...`) rather than silently ignoring them.

  ## What could still silently go wrong

  1. `Val.beq` now compares two `bobj`s, and a `bobj` against a plain builtin, by
     **contents, ignoring the class**. That is CPython's behaviour for `tuple`/`list`/
     `dict`/`str` subclasses that do not override `__eq__` (measured: `A((0,)) ==
     B((0,))` is `True`), and the `__eq__` check at construction is what keeps it true.
     If a future exporter records a builtin base for a class whose `__eq__` it could not
     see, equality would be wrong and nothing here would catch it.
  2. Mutation of a `list`/`dict` base is value-semantics, exactly as Core's own
     containers already are (`setIndex` is `setIndex:immutable-containers`). A `bobj`
     inherits that known unsoundness rather than adding a new one — see
     `docs/boxed-containers.md`.
  3. Any `match` on `Val` with a catch-all that predates this constructor will treat a
     `bobj` as "some other value". Every such site in `Semantics.lean` and `Stdlib.lean`
     was audited; a site added later will not be. -/
  | bobj  : String → Val → Val
  deriving Repr, Inhabited

/-- The builtin types a user class may inherit from and still be modelled.

Deliberately not `Exception` (Core represents exceptions as bare `Val.str` class names,
so an exception subclass has nowhere to put its payload), not `object` (that is an
ordinary class and already works), and not multiple bases. -/
inductive BuiltinBase where
  | tuple
  | list
  | dict
  | str
  deriving Repr, Inhabited, DecidableEq

namespace BuiltinBase

/-- The empty instance of the base, used when the constructor is called with no
argument: `tuple()` is `()`, `str()` is `""`. -/
def empty : BuiltinBase → Val
  | .tuple => .tuple []
  | .list  => .list []
  | .dict  => .dict []
  | .str   => .str ""

/-- The builtin type name, for `isinstance`. -/
def typeName : BuiltinBase → String
  | .tuple => "tuple"
  | .list  => "list"
  | .dict  => "dict"
  | .str   => "str"

end BuiltinBase

/-- A heap object: its class and its mutable fields. -/
structure Obj where
  cls    : String
  fields : List (String × Val)
  /-- Bindings captured by the class that produced this object, if it was defined inside
  a function. Resolved after the object's own fields and before globals. -/
  captured : List (String × Val) := []
  deriving Repr, Inhabited

/-- The heap. Index into the list is the `Ref`; allocation appends. -/
abbrev Heap := List Obj

namespace Heap

/-- Dereference. -/
def get (h : Heap) (r : Ref) : Option Obj := h[r]?

/-- Allocate, returning the new heap and the fresh reference. -/
def alloc (h : Heap) (o : Obj) : Heap × Ref := (h ++ [o], h.length)

/-- Read a field, `unit` if absent. -/
def getField (h : Heap) (r : Ref) (f : String) : Val :=
  match h.get r with
  | none   => .unit
  | some o => match o.fields.find? (·.1 == f) with
              | some (_, v) => v
              | none        => .unit

/-- Write a field, shadowing any previous binding. -/
def setField (h : Heap) (r : Ref) (f : String) (v : Val) : Heap :=
  h.mapIdx fun i o => if i == r then { o with fields := (f, v) :: o.fields } else o

end Heap

/-- Literals as they appear in source. -/
inductive Lit where
  | int   : Int → Lit
  | str   : String → Lit
  | bool  : Bool → Lit
  /-- A float literal. The transpiler should emit the *bit pattern*
  (`Fl.ofBits 4591870180066957722` for `0.1`), not decimal text: `Format.ofDecimal` can
  correctly round a decimal literal, but going back out to decimal is not modelled, so
  bits are the only spelling that round-trips through the differential harness. -/
  | float : Fl → Lit
  | unit  : Lit
  deriving Repr, Inhabited, DecidableEq

/-- Expressions. `call` is by name: the CPG gives us resolved callee names. -/
inductive Expr where
  | lit    : Lit → Expr
  | name   : String → Expr
  | binop  : String → Expr → Expr → Expr
  | unop   : String → Expr → Expr
  | call   : String → List Expr → Expr
  | index  : Expr → Expr → Expr
  /-- Attribute access: `e.f`. -/
  | field  : Expr → String → Expr
  /-- Method call on a receiver: `e.m(args)`. Dispatch is on the receiver's class. -/
  | mcall  : Expr → String → List Expr → Expr
  /-- Object construction: `Cls(args)`, running `Cls.__init__` if one is known. -/
  | alloc  : String → List Expr → Expr
  /-- A function, method or class used as a value (`METHOD_REF` / `TYPE_REF`). -/
  | fnref  : String → Expr
  /-- A function value that captures the enclosing scope: decorators, factories, and
  nested functions that read outer variables. -/
  | closure : String → Expr
  /-- A *class* value that captures the enclosing scope. Distinct from `closure` because
  a class is not a function: its methods, not it, read the captured bindings. -/
  | classClosure : String → Expr
  | listE  : List Expr → Expr
  | tupleE : List Expr → Expr
  | dictE  : List (Expr × Expr) → Expr
  /-- Conditional expression `t if c else e`. -/
  | cond   : Expr → Expr → Expr → Expr
  /-- Reference identity. `true` means negated (`is not`). -/
  | isOp   : Bool → Expr → Expr → Expr
  /-- Membership. `true` means negated (`not in`). -/
  | inOp   : Bool → Expr → Expr → Expr
  -- ### Argument forms
  --
  -- Python's calling convention needs three argument *shapes* that a fixed positional
  -- list cannot express. They are added as `Expr` constructors rather than by changing
  -- `call`'s argument type, because replacing `List Expr` with a new `Arg` type makes
  -- every one of the ~110 existing `Expr` matches non-exhaustive at once, while three new
  -- leaf constructors only disturb the handful of matches that are exhaustive.
  --
  -- They are only meaningful directly inside a call's argument list. `evalList` -- the
  -- one place an argument list is evaluated -- dispatches on them; `evalExpr` reached on
  -- one of them anywhere else yields the hole `op:starred-outside-call`, which is an
  -- honest admission rather than a silently wrong value.
  /-- `*e` in an argument list: splice the elements of an iterable into the positional
  arguments. A non-iterable operand raises `TypeError`, as in CPython. -/
  | starred : Expr → Expr
  /-- `k = e` in an argument list: one keyword argument. Before this existed the exporter
  dropped such arguments **silently** — `_wrapper(..., info = make_info)` translated to a
  call that simply did not pass `info`. -/
  | kwargE  : String → Expr → Expr
  /-- `**e` in an argument list: splice a `dict` into the keyword arguments. Non-`dict`
  operands, and `dict`s with non-string keys, raise `TypeError`, as in CPython. -/
  | dstarred : Expr → Expr
  /-- Unmapped expression, tagged with the originating CPG node label. -/
  | hole   : String → Expr
  deriving Repr, Inhabited

/-- Statements. -/
inductive Stmt where
  | skip     : Stmt
  | expr     : Expr → Stmt
  | assign   : String → Expr → Stmt
  /-- `e.f = v` -/
  | setField : Expr → String → Expr → Stmt
  /-- `e[i] = v` -/
  | setIndex : Expr → Expr → Expr → Stmt
  | seq      : Stmt → Stmt → Stmt
  | ifte     : Expr → Stmt → Stmt → Stmt
  | loop     : Expr → Stmt → Stmt
  /-- `for x in e: body` -/
  | forIn    : String → Expr → Stmt → Stmt
  | ret      : Expr → Stmt
  | brk      : Stmt
  | cont     : Stmt
  /-- `try: body except as x: handler`. Catches exceptions only — `ret`/`brk`/`cont`
  pass straight through, or every `try/except` containing a `return` would break. -/
  | tryCatch : Stmt → String → Stmt → Stmt
  /-- `try: body finally: fin`. The finalizer runs on **every** exit path, and an
  abnormal exit from the finalizer discards the pending outcome of the body — Python's
  rule, so `try: return 1 finally: return 2` returns 2. -/
  | tryFinally : Stmt → Stmt → Stmt
  | raise    : Expr → Stmt
  /-- `del x` -/
  | del      : String → Stmt
  /-- Write a module-level binding: `x = e` at module scope, or under `global x`. -/
  | setGlobal   : String → Expr → Stmt
  /-- `global x` — subsequent assignments to `x` in this function target module scope. -/
  | declGlobal  : String → Stmt
  /-- Unmapped statement, tagged with the originating CPG node label. -/
  | hole     : String → Stmt
  deriving Repr, Inhabited

/-- A function: name, parameters, body.

`params` lists **every** parameter name in source order, including the variadic ones.
`vararg` and `kwarg` say which of those names — if any — are `*args` and `**kwargs`; they
are `Option`al fields with `none` defaults, so every existing `Func` literal and every
already-rendered corpus keeps its meaning unchanged. See `bindParams` in `Semantics.lean`
for the binding rule. -/
structure Func where
  name   : String
  params : List String
  body   : Stmt
  /-- The `*args` parameter's name, if the function has one. -/
  vararg : Option String := none
  /-- The `**kwargs` parameter's name, if the function has one. -/
  kwarg  : Option String := none
  deriving Repr, Inhabited

/-- Whether this `Func` is a method, by the exporter's naming convention: the segment after
`<module>.` is `Class.method` rather than a bare function name. Used to recover Python's
unbound-method rule, where a method reached as a plain value takes its receiver as the
first positional argument. -/
def Func.isMethod (fn : Func) : Bool :=
  match fn.name.splitOn "<module>." with
  | [_, rest] => rest.any (· == '.')
  | _         => false

/-- A whole translated codebase, tagged with the dialect it came from. -/
structure Program where
  funcs   : List Func
  dialect : Dialect := .python
  /-- Classes whose (single) base is a builtin type, by the **short** class name that
  `Expr.alloc` uses. Empty by default, so a program translated before the exporter
  learned to record bases behaves exactly as it did: opaque `Val.ref` instances.

  Keyed by short name because that is what the CPG gives the allocation site. A corpus
  with two same-named classes in different modules and *different* bases cannot be
  represented; the exporter drops such a name entirely rather than guessing, which
  degrades to the pre-existing opaque-reference behaviour. -/
  builtinBases : List (String × BuiltinBase) := []
  deriving Repr, Inhabited

namespace Expr

/-- Is this an ordinary argument — one that contributes exactly one positional value —
rather than one of the three starred forms? Used as the side condition on the reasoning
lemmas about argument lists. -/
def plainArg : Expr → Bool
  | .starred _  => false
  | .kwargE _ _ => false
  | .dstarred _ => false
  | _           => true

/-!
Nested inductives (`List Expr`, `List (Expr × Expr)`) need explicit list helpers for
Lean to see the recursion as structural — `List.flatMap` hides it.
-/
mutual
/-- Holes in an expression, by label. -/
def holes : Expr → List String
  | .hole l       => [l]
  | .binop _ a b  => holes a ++ holes b
  | .unop _ a     => holes a
  | .index a b    => holes a ++ holes b
  | .field a _    => holes a
  | .call _ as    => holesL as
  | .mcall r _ as => holes r ++ holesL as
  | .alloc _ as   => holesL as
  | .listE as     => holesL as
  | .tupleE as    => holesL as
  | .dictE kvs    => holesP kvs
  | .cond c a b   => holes c ++ holes a ++ holes b
  | .isOp _ a b   => holes a ++ holes b
  | .inOp _ a b   => holes a ++ holes b
  | .starred a    => holes a
  | .kwargE _ a   => holes a
  | .dstarred a   => holes a
  | _             => []

/-- Holes across a list of expressions. -/
def holesL : List Expr → List String
  | []      => []
  | e :: es => holes e ++ holesL es

/-- Holes across a list of key/value expression pairs. -/
def holesP : List (Expr × Expr) → List String
  | []           => []
  | (k, v) :: ps => holes k ++ holes v ++ holesP ps
end

mutual
/-- Total node count, for coverage arithmetic. -/
def size : Expr → Nat
  | .binop _ a b  => 1 + size a + size b
  | .unop _ a     => 1 + size a
  | .index a b    => 1 + size a + size b
  | .field a _    => 1 + size a
  | .call _ as    => 1 + sizeL as
  | .mcall r _ as => 1 + size r + sizeL as
  | .alloc _ as   => 1 + sizeL as
  | .listE as     => 1 + sizeL as
  | .tupleE as    => 1 + sizeL as
  | .dictE kvs    => 1 + sizeP kvs
  | .cond c a b   => 1 + size c + size a + size b
  | .isOp _ a b   => 1 + size a + size b
  | .inOp _ a b   => 1 + size a + size b
  | .starred a    => 1 + size a
  | .kwargE _ a   => 1 + size a
  | .dstarred a   => 1 + size a
  | _             => 1

/-- Node count across a list of expressions. -/
def sizeL : List Expr → Nat
  | []      => 0
  | e :: es => size e + sizeL es

/-- Node count across a list of key/value expression pairs. -/
def sizeP : List (Expr × Expr) → Nat
  | []           => 0
  | (k, v) :: ps => size k + size v + sizeP ps
end

end Expr

namespace Stmt

/-- Holes in a statement, by label. -/
def holes : Stmt → List String
  | .hole l          => [l]
  | .expr e          => e.holes
  | .assign _ e      => e.holes
  | .setField r _ v  => r.holes ++ v.holes
  | .setIndex r i v  => r.holes ++ i.holes ++ v.holes
  | .seq a b         => a.holes ++ b.holes
  | .ifte c a b      => c.holes ++ a.holes ++ b.holes
  | .loop c a        => c.holes ++ a.holes
  | .forIn _ e b     => e.holes ++ b.holes
  | .ret e           => e.holes
  | .tryCatch b _ h  => b.holes ++ h.holes
  | .tryFinally b f  => b.holes ++ f.holes
  | .raise e         => e.holes
  | .setGlobal _ e   => e.holes
  | _                => []

/-- Total node count. -/
def size : Stmt → Nat
  | .expr e          => 1 + e.size
  | .assign _ e      => 1 + e.size
  | .setField r _ v  => 1 + r.size + v.size
  | .setIndex r i v  => 1 + r.size + i.size + v.size
  | .seq a b         => a.size + b.size
  | .ifte c a b      => 1 + c.size + a.size + b.size
  | .loop c a        => 1 + c.size + a.size
  | .forIn _ e b     => 1 + e.size + b.size
  | .ret e           => 1 + e.size
  | .tryCatch b _ h  => 1 + b.size + h.size
  | .tryFinally b f  => 1 + b.size + f.size
  | .raise e         => 1 + e.size
  | .setGlobal _ e   => 1 + e.size
  | _                => 1

end Stmt

namespace Func
/-- Holes in a function. -/
def holes (f : Func) : List String := f.body.holes
/-- Node count of a function. -/
def size (f : Func) : Nat := f.body.size
/-- A function is *fully translated* when it contains no holes. Only these are
candidates for unconditional verification. -/
def total (f : Func) : Bool := f.holes.isEmpty
end Func

namespace Program
/-- Every hole in the program. -/
def holes (p : Program) : List String := p.funcs.flatMap Func.holes
/-- Total node count. -/
def size (p : Program) : Nat := (p.funcs.map Func.size).sum
/-- Functions with no holes — the verifiable core. -/
def verifiableCore (p : Program) : List Func := p.funcs.filter Func.total
end Program

/-!
Structural equality on values is written by hand: the nested `List`/`Prod` occurrences
block `deriving DecidableEq`.
-/
mutual
/-- Structural equality on values. -/
def Val.beq : Val → Val → Bool
  | .int a,   .int b   => a == b
  | .str a,   .str b   => a == b
  | .bool a,  .bool b  => a == b
  -- Floats compare by *value*, never by bit pattern: `nan != nan`, `+0.0 == -0.0`.
  | .float a, .float b => Fl.eqv a b
  -- Python's numeric tower: `1 == 1.0`, and `{1: 'a'}[1.0]` succeeds because the two also
  -- hash equal. The comparison is *exact* — `10**23 == 1e23` is `False` in CPython —
  -- which is why it goes through `Fl.cmpIntv` rather than converting either side.
  | .int a,   .float b => Fl.cmpIntv a b == some .eq
  | .float a, .int b   => Fl.cmpIntv b a == some .eq
  | .unit,    .unit    => true
  | .ref a,   .ref b   => a == b
  | .fn a,    .fn b    => a == b
  | .clos a _, .clos b _ => a == b
  | .clsClos a _, .clsClos b _ => a == b
  | .list a,  .list b  => Val.beqL a b
  | .tuple a, .tuple b => Val.beqL a b
  | .dict a,  .dict b  => Val.beqP a b
  -- Instances of builtin-based classes compare by **contents, ignoring the class**, and
  -- compare equal to the plain builtin. Measured against CPython 3.9.6:
  --   `A((0,)) == (0,)`  True      `A((0,)) == B((0,))`  True   (A, B both `(tuple)`)
  --   `A((0,)) == (1,)`  False     `A((0,)) == [0]`      False
  -- The twelve cases are written out rather than routed through an unwrapping helper so
  -- that every recursive call is on a *subterm of the first argument*: that is what keeps
  -- `Val.beq` structurally recursive, and hence reducible by `rfl`/`decide`, which the
  -- float equations below and much of `Refine.lean` depend on.
  | .bobj _ (.tuple a), .bobj _ (.tuple b) => Val.beqL a b
  | .bobj _ (.list a),  .bobj _ (.list b)  => Val.beqL a b
  | .bobj _ (.dict a),  .bobj _ (.dict b)  => Val.beqP a b
  | .bobj _ (.str a),   .bobj _ (.str b)   => a == b
  | .bobj _ (.tuple a), .tuple b => Val.beqL a b
  | .bobj _ (.list a),  .list b  => Val.beqL a b
  | .bobj _ (.dict a),  .dict b  => Val.beqP a b
  | .bobj _ (.str a),   .str b   => a == b
  | .tuple a, .bobj _ (.tuple b) => Val.beqL a b
  | .list a,  .bobj _ (.list b)  => Val.beqL a b
  | .dict a,  .bobj _ (.dict b)  => Val.beqP a b
  | .str a,   .bobj _ (.str b)   => a == b
  | _,        _        => false
/-- Structural equality on value lists. -/
def Val.beqL : List Val → List Val → Bool
  | [],      []      => true
  | a :: as, b :: bs => Val.beq a b && Val.beqL as bs
  | _,       _       => false
/-- Structural equality on key/value lists. -/
def Val.beqP : List (Val × Val) → List (Val × Val) → Bool
  | [],           []           => true
  | (a,b) :: as, (c,d) :: bs   => Val.beq a c && Val.beq b d && Val.beqP as bs
  | _,           _             => false
end

instance : BEq Val := ⟨Val.beq⟩

/-- Strip one layer of builtin-base wrapping: the underlying `tuple`/`list`/`dict`/`str`
of an instance of a class with a builtin base, or the value unchanged.

Only one layer is ever needed: `Expr.alloc` never builds a `bobj` whose payload is itself
a `bobj` (the payload is coerced to the declared base first).

Deliberately **non-recursive**. Every consumer below unwraps with this rather than
recursing on `Val`, which keeps `Val.truthy`, `Val.iterable` and `Stdlib.elems`
non-recursive matchers: making them recursive compiles them through `brecOn`, and the
`unfold`/`whnf`-based proof of `Stdlib.builtin_heap_unchanged` does not survive that. -/
def Val.unbuiltin : Val → Val
  | .bobj _ v => v
  | v         => v

/-- Truthiness, in the permissive sense shared by most dynamic languages. -/
def Val.truthy : Val → Bool
  | .bool b   => b
  | .int i    => i != 0
  | .str s    => s != ""
  -- `bool(0.0) == bool(-0.0) == False`; `bool(nan)` is `True`.
  | .float f  => Fl.truthy f
  | .unit     => false
  | .list vs  => !vs.isEmpty
  | .tuple vs => !vs.isEmpty
  | .dict kvs => !kvs.isEmpty
  | .ref _    => true
  | .fn _     => true
  | .clos _ _ => true
  | .clsClos _ _ => true
  -- An instance of a class with a builtin base is truthy exactly as its base is:
  -- `bool(A(()))` is `False` for `class A(tuple)`. Written out per base rather than
  -- recursing, so this stays a plain matcher that reduces by `rfl`.
  | .bobj _ (.list vs)  => !vs.isEmpty
  | .bobj _ (.tuple vs) => !vs.isEmpty
  | .bobj _ (.dict kvs) => !kvs.isEmpty
  | .bobj _ (.str t)    => t != ""
  | .bobj _ _           => true

/-- What a value iterates over, if anything.

A `str` iterates over its characters as **one-character strings**, as CPython does:
`list("ab") == ['a', 'b']` and `g(*"ab") == ('a', 'b')` under CPython 3.9.6. Core had no
`str` case at all, which made `g(*"ab")` a `TypeError` and `for c in "ab"` a hole — a
measured divergence on extremely common code, recorded as a theorem until this change
and now recorded as agreement (`CallingConvention.str_is_iterable`).

The encoding is character-for-character the one `Stdlib.elems` already used for `str`,
which is what made the omission here a plain inconsistency rather than a design choice:
`list("ab")` worked while `for c in "ab"` did not. `String.toList` is the codepoint
decomposition, so this iterates `Char`s as CPython 3 iterates a `str`, not bytes.

Note the base case: the empty string iterates to `[]`, so `g(*"")` is `()` — matching
CPython — rather than an error, and a `str` case that returned `some []` for *every*
string would satisfy that pin while being useless, which is why the non-empty case is
pinned separately. -/
def Val.iterable : Val → Option (List Val)
  | .list vs  => some vs
  | .tuple vs => some vs
  | .dict kvs => some (kvs.map (·.1))
  | .str s    => some (s.toList.map (fun c => .str c.toString))
  | .bobj _ (.list vs)  => some vs
  | .bobj _ (.tuple vs) => some vs
  | .bobj _ (.dict kvs) => some (kvs.map (·.1))
  | .bobj _ (.str s)    => some (s.toList.map (fun c => .str c.toString))
  | _         => none

/-- Result of evaluating an expression. -/
inductive EResult where
  | val       : Val → EResult
  /-- A raised exception carrying its payload. -/
  | exn       : Val → EResult
  | hole      : String → EResult
  | outOfFuel : EResult
  deriving Repr, Inhabited

end Autoform.Core
