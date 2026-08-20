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
  deriving Repr, Inhabited

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

/-- A function: name, parameters, body. -/
structure Func where
  name   : String
  params : List String
  body   : Stmt
  deriving Repr, Inhabited

/-- A whole translated codebase, tagged with the dialect it came from. -/
structure Program where
  funcs   : List Func
  dialect : Dialect := .python
  deriving Repr, Inhabited

namespace Expr

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

/-- What a value iterates over, if anything. -/
def Val.iterable : Val → Option (List Val)
  | .list vs  => some vs
  | .tuple vs => some vs
  | .dict kvs => some (kvs.map (·.1))
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
