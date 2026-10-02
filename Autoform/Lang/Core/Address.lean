import Autoform.Lang.Core.Syntax

/-!
# Core — the C address model

C pointer comparison and arithmetic are statements about *objects*: two pointers are
ordered only when they point into the same array object (C11 6.5.8p5), a pointer may be
formed one past the end of an array but not further (6.5.6p8), and equality is defined
across objects -- except that a pointer one past the end of one object may or may not
compare equal to a pointer to the start of an object that happens to follow it
(6.5.9p6, footnote 109). None of that can be answered from two values alone, which is
why `applyBinop` (heap-free, and the function `Refine.lean`'s reducible lemmas are about)
cannot be the place it lives. This file is.

## The model

Provenance-based, after CompCert's `Vptr b ofs` and CH2O's object-path pointers: a
pointer is a **block** (a heap `Ref`) plus an **offset** within it. Core already had the
values; what it lacked was the block's *extent* and *element size*, and the operations
that consult them.

| C pointer | Core value |
|---|---|
| element `i` of array object `r` (incl. one-past-the-end, `i = extent`) | `Val.iref r (.idx i)` |
| member `f` of struct object `r` / a boxed scalar | `Val.iref r (.fld f)` |
| the whole object `r` | `Val.ref r` |
| null | `Val.unit` (spelled `NULL`/`(T*)0`) or `Val.int 0` (spelled `0`) |
| a `char*` under the string model | `Val.str s` -- the bytes up to the terminator; **no identity** |
| a function | `Val.fn f` |

* **Extent** (`Heap.extent`): every array block Core allocates (`Expr.boxArray`, the
  exporter's `boxFieldsRange`) holds the decimal keys `"0" … "n-1"` and nothing writes a
  numeric key outside them -- `setDerefIref` refuses an out-of-bounds index -- so the
  number of contiguous decimal keys from `"0"` is the array's length.
* **Element size** (`Heap.elemSize`): an in-band field `"$esz"` (a key no C identifier
  can spell, the same convention as the exporter's `$off` locals) recording the byte size
  the block's elements were allocated with. Untagged blocks have no element size, and
  stride-dependent arithmetic on them is a hole.

## What is answered and what is a hole

`applyPtrOp` answers exactly where ISO C defines the answer and Core knows it:

* `==`/`!=`: null vs null, null vs any object pointer, same block (offsets compared),
  different blocks when neither pointer is one-past-the-end (false). One-past-the-end
  against another block is **unspecified** → `ptr:eq-one-past-unspecified`.
* `<`/`<=`/`>`/`>=`: same block, both offsets within `[0, extent]` → offsets compared.
  Different blocks, or anything involving null → `ub:ptr-compare-cross-object` /
  `ub:ptr-order-null` (undefined behaviour). Struct members: equality only (Core does
  not know member order).
* `+`/`-` (pointer ± integer) and `diff` (pointer − pointer): same block, the static
  pointee size equal to the block's element size, every offset involved within
  `[0, extent]`. Leaving the array is undefined behaviour → `ub:ptr-arith-out-of-bounds`;
  a stride mismatch → `ptr:stride-mismatch`; an untagged block → `ptr:untyped-block`.
  A `Val.str` advances under the string model (`drop k`) for byte strides only, ASCII
  only (a `String` is indexed by code point, not byte), and never past the terminator
  (the bytes beyond it are not in the value).
* `Val.str` has no address, so any comparison involving one (other than the null test,
  which the exporter emits separately) is `str:pointer-compare-not-modelled` /
  `str:pointer-equality-not-modelled`, the labels the heap-free path already used.

## Member boxes

The exporter boxes an ARRAY member of a boxed struct as its own block, so the C address of
that member has two Core spellings: `&s.arr` (`Val.iref s (.fld "arr")`) and `s.arr`
decayed (a pointer into the member's block) -- and if `arr` is the first member, `&s`
shares it too. "Different blocks" therefore does not mean "different addresses" for a
member box. The exporter marks such blocks (`"$member"`, `Heap.isMemberBox`), and any
cross-block equality involving one, or between a member selector and its own nested box
(`Heap.memberBoxIs`), is `ptr:member-box-alias` rather than `false`.

## Pointer ↔ integer

**Hole, not an encoding.** C11 6.3.2.3p5–6 make both directions implementation-defined,
and a Core block has no numeric address: any integer Core produced for `(uintptr_t)p`
would be invented. An abstract encoding (a "pointer-valued integer" carrying provenance,
as in the PNVI proposals) would support only round trips and equality, and SQLite's uses
of `SQLITE_PTR_TO_INT` hash, align (`& 7`) or subtract the bits -- all of which would be
holes anyway, at the cost of a new `Val` constructor every match in Core would have to
learn. So `(intT)p` stays `applyUnop "cast:<w>"` on a non-integer, a hole; and
`(T*)n` for a non-zero integer `n` is a hole (`ptrCast`).

`ptrCast` is the *dynamic* form of the exporter's pointer-to-pointer pass-through: a
cast to a pointer type whose operand's static type the frontend could not resolve. If the
operand is a pointer at run time the cast is the identity (Core pointer values carry no C
type, the argument `castOperandIsPointerShaped` already makes statically); if it is an
integer it is the int-to-pointer conversion above, a hole. The null pointer `0` passes as
itself: it is already one of the two spellings of null in this model.
-/

namespace Autoform.Core

namespace Heap

/-- Does block `r` carry key `k`? `false` for a dangling ref. -/
def hasKey (h : Heap) (r : Ref) (k : String) : Bool :=
  match h.get r with
  | none   => false
  | some o => o.fields.any (·.1 == k)

/-- Count the contiguous decimal keys `"i"`, `"i+1"`, … of `o`, at most `fuel` of them.
Each step consumes a key that is present, so `o.fields.length` is enough fuel. -/
def extentGo (o : Obj) : Nat → Nat → Nat
  | 0,     i => i
  | f + 1, i => if o.fields.any (·.1 == toString i) then extentGo o f (i + 1) else i

/-- The length of array block `r`: its contiguous decimal keys from `"0"`. -/
def extent (h : Heap) (r : Ref) : Nat :=
  match h.get r with
  | none   => 0
  | some o => extentGo o o.fields.length 0

/-- The byte size the elements of block `r` were allocated with, if recorded. -/
def elemSize (h : Heap) (r : Ref) : Option Nat :=
  match h.getField r "$esz" with
  | .int n => if n > 0 then some n.toNat else none
  | _      => none

end Heap

/-- Where an element offset lies relative to its block. -/
inductive PtrPos where
  /-- `0 ≤ i < extent`: a dereferenceable element. -/
  | inside
  /-- `i = extent`: one past the end -- a valid pointer value, not dereferenceable. -/
  | onePast
  /-- Anything else, or a dangling block: forming this pointer was already UB. -/
  | outside
  deriving Repr, DecidableEq

/-- Classify offset `i` in block `r`. -/
def Heap.idxPos (h : Heap) (r : Ref) (i : Int) : PtrPos :=
  match h.get r with
  | none   => .outside
  | some _ =>
    let n : Int := h.extent r
    if 0 ≤ i ∧ i < n then .inside else if i = n then .onePast else .outside

/-- Classify a selector. A member selector names an existing member (Core never forms
one-past-the-end of a struct member: `iref:arith-on-field`). -/
def Heap.selPos (h : Heap) (r : Ref) : Sel → PtrPos
  | .idx i => h.idxPos r i
  | .fld _ => if (h.get r).isSome then .inside else .outside

/-- How Core represents the pointer a value denotes. -/
inductive PtrView where
  | null
  | blk   : Ref → Sel → PtrView
  | whole : Ref → PtrView
  | str   : String → PtrView
  | fn    : String → PtrView
  | other

/-- Read a value as a pointer. -/
def PtrView.of : Val → PtrView
  | .unit      => .null
  | .int n     => if n == 0 then .null else .other
  | .iref r s  => .blk r s
  | .ref r     => .whole r
  | .str s     => .str s
  | .fn f      => .fn f
  | _          => .other

/-- Is `op` one of the two equality operators? -/
def ptrIsEq (op : String) : Bool := op == "==" || op == "!="

/-- The answer to `==`/`!=` given whether the two pointers are the same. -/
def ptrEqAns (op : String) (same : Bool) : EResult :=
  .val (.bool (if op == "==" then same else !same))

/-- Compare two offsets in one block. -/
def ptrRelInts (op : String) (i j : Int) : EResult :=
  match op with
  | "==" => .val (.bool (i == j))
  | "!=" => .val (.bool (i != j))
  | "<"  => .val (.bool (decide (i < j)))
  | "<=" => .val (.bool (decide (i ≤ j)))
  | ">"  => .val (.bool (decide (i > j)))
  | ">=" => .val (.bool (decide (i ≥ j)))
  | _    => .hole s!"ptrOp:{op}"

/-- Two pointers into DIFFERENT blocks (or a block and a whole other object). Ordering is
undefined; equality is `false` unless one of them is one past the end of its array, in
which case C does not say. -/
def ptrRelCross (op : String) (pa pb : PtrPos) : EResult :=
  if !ptrIsEq op then .hole "ub:ptr-compare-cross-object"
  else if pa == .outside || pb == .outside then .hole "ub:ptr-out-of-bounds"
  else if pa == .onePast || pb == .onePast then .hole "ptr:eq-one-past-unspecified"
  else ptrEqAns op false

/-- Does selector `s` of block `r` name a member whose value is a NESTED box, block `q`?
Then `&r.f` and a pointer into `q` are two Core spellings of one C address (the exporter
boxes an array member separately, `boxedStructArrayMembers`), and the blocks differing
says nothing. -/
def Heap.memberBoxIs (h : Heap) (r : Ref) (s : Sel) (q : Ref) : Bool :=
  match s with
  | .fld f => match h.getField r f with
              | .ref q'    => q' == q
              | .iref q' _ => q' == q
              | _          => false
  | .idx _ => false

/-- Is block `r` an array MEMBER boxed separately from its struct (`"$member"`, set by
the exporter)? Its address coincides with a member address of another block, so "different
blocks" does not mean "different addresses" for it. -/
def Heap.isMemberBox (h : Heap) (r : Ref) : Bool :=
  match h.getField r "$member" with
  | .bool b => b
  | _       => false

/-- Two different blocks whose addresses could coincide although they are different blocks:
one is a nested member box of the other, or either is a member box at all. -/
def Heap.mayAlias (h : Heap) (r : Ref) (s : Sel) (q : Ref) (t : Option Sel) : Bool :=
  h.isMemberBox r || h.isMemberBox q || h.memberBoxIs r s q ||
  (match t with | some t => h.memberBoxIs q t r | none => false)

/-- `a op b` for a relational or equality operator on two pointer values. -/
def ptrRel (h : Heap) (op : String) (a b : Val) : EResult :=
  match PtrView.of a, PtrView.of b with
  | .other, _ | _, .other => .hole "ptr:non-pointer-operand"
  | .null, .null => if ptrIsEq op then ptrEqAns op true else .hole "ub:ptr-order-null"
  | .null, .str _ | .str _, .null
  | .null, .fn _  | .fn _, .null
  | .null, .whole _ | .whole _, .null =>
      if ptrIsEq op then ptrEqAns op false else .hole "ub:ptr-order-null"
  | .null, .blk r s | .blk r s, .null =>
      if !ptrIsEq op then .hole "ub:ptr-order-null"
      else if h.selPos r s == .outside then .hole "ub:ptr-out-of-bounds"
      else ptrEqAns op false
  | .str _, _ | _, .str _ =>
      if ptrIsEq op then .hole "str:pointer-equality-not-modelled"
      else .hole "str:pointer-compare-not-modelled"
  | .fn f, .fn g =>
      -- Equal names are the same function. Distinct names are NOT known to be distinct
      -- functions (a call site and a definition may spell one function differently).
      if ptrIsEq op && f == g then ptrEqAns op true else .hole "ptr:fn-identity"
  | .fn _, _ | _, .fn _ => .hole "ptr:fn-vs-object"
  | .whole r, .whole q =>
      if r == q then ptrRelInts op 0 0
      else if !ptrIsEq op then .hole "ub:ptr-compare-cross-object"
      else if h.isMemberBox r || h.isMemberBox q then .hole "ptr:member-box-alias"
      else ptrEqAns op false
  | .whole r, .blk q s =>
      if r != q && h.mayAlias q s r none then .hole "ptr:member-box-alias"
      else if r != q then ptrRelCross op .inside (h.selPos q s)
      else match s with
        | .idx i => if h.idxPos q i == .outside then .hole "ub:ptr-out-of-bounds"
                    else ptrRelInts op 0 i
        | .fld _ => .hole "ptr:whole-vs-member"
  | .blk r s, .whole q =>
      if r != q && h.mayAlias r s q none then .hole "ptr:member-box-alias"
      else if r != q then ptrRelCross op (h.selPos r s) .inside
      else match s with
        | .idx i => if h.idxPos r i == .outside then .hole "ub:ptr-out-of-bounds"
                    else ptrRelInts op i 0
        | .fld _ => .hole "ptr:whole-vs-member"
  | .blk r s, .blk q t =>
      if r != q && h.mayAlias r s q (some t) then .hole "ptr:member-box-alias"
      else if r != q then ptrRelCross op (h.selPos r s) (h.selPos q t)
      else match s, t with
        | .idx i, .idx j =>
            if h.idxPos r i == .outside || h.idxPos r j == .outside then .hole "ub:ptr-out-of-bounds"
            else ptrRelInts op i j
        | .fld f, .fld g =>
            if ptrIsEq op then ptrEqAns op (f == g) else .hole "ptr:member-order"
        | _, _ => .hole "ptr:mixed-selector"

/-- Is every character of `s` ASCII (so that code-point offsets are byte offsets)? -/
def ptrAsciiOnly (s : String) : Bool := s.toList.all (fun c => c.toNat < 128)

/-- `p + k` for a pointer whose static pointee is `esz` bytes. -/
def ptrAdd (h : Heap) (esz : Nat) (p : Val) (k : Int) : EResult :=
  match p with
  | .iref r (.idx i) =>
      match h.elemSize r with
      | none => .hole "ptr:untyped-block"
      | some e =>
          if e != esz then .hole "ptr:stride-mismatch"
          else if h.idxPos r i == .outside || h.idxPos r (i + k) == .outside then
            .hole "ub:ptr-arith-out-of-bounds"
          else .val (.iref r (.idx (i + k)))
  | .iref _ (.fld _) => .hole "iref:arith-on-field"
  | .str s =>
      if esz != 1 then .hole "ptr:stride-mismatch"
      else if !ptrAsciiOnly s then .hole "ptr:str-non-ascii"
      else if k < 0 then .hole "ptr:str-before-start"
      else if k > s.length then .hole "ptr:str-past-terminator"
      else .val (.str (String.ofList (s.toList.drop k.toNat)))
  | .unit  => .hole "ub:ptr-arith-null"
  | .int 0 => .hole "ub:ptr-arith-null"
  | _      => .hole "ptr:arith-non-pointer"

/-- `p - q` for two pointers whose static pointee is `esz` bytes, in elements. -/
def ptrDiff (h : Heap) (esz : Nat) (a b : Val) : EResult :=
  match a, b with
  | .iref r (.idx i), .iref q (.idx j) =>
      if r != q then .hole "ub:ptr-diff-cross-object"
      else match h.elemSize r with
        | none => .hole "ptr:untyped-block"
        | some e =>
            if e != esz then .hole "ptr:stride-mismatch"
            else if h.idxPos r i == .outside || h.idxPos r j == .outside then
              .hole "ub:ptr-out-of-bounds"
            else .val (.int (i - j))
  | .str _, _ | _, .str _ => .hole "str:pointer-arithmetic-not-modelled"
  | _, _ => .hole "ptr:diff-non-index"

/-- The semantics of `Expr.ptrOp op esz a b`, given the two operand values. -/
def applyPtrOp (h : Heap) (op : String) (esz : Nat) (a b : Val) : EResult :=
  match op with
  | "+"    => match b with
              | .int k => ptrAdd h esz a k
              | _      => .hole "ptr:offset-non-int"
  | "-"    => match b with
              | .int k => ptrAdd h esz a (-k)
              | _      => .hole "ptr:offset-non-int"
  | "diff" => ptrDiff h esz a b
  | _      => ptrRel h op a b

/-- `(T*)e` where the exporter could not resolve `e`'s static type: the identity on every
pointer value, the null pointer `0` included, and a hole on any other integer (an
implementation-defined int-to-pointer conversion Core has no address for). -/
def ptrCast : Val → EResult
  | .unit      => .val .unit
  | .int n     => if n == 0 then .val (.int 0) else .hole "op:cast:pointer:int-to-pointer"
  | .iref r s  => .val (.iref r s)
  | .ref r     => .val (.ref r)
  | .str s     => .val (.str s)
  | .fn f      => .val (.fn f)
  | _          => .hole "op:cast:pointer:non-pointer"

/-! ## Checks

A small heap: block 0 is a 3-byte array (`u8 a[3]`), block 1 a 2-element array of 4-byte
ints, block 2 a struct with members `x`, `y`. -/

private def tA : Obj :=
  { cls := "<local>", fields := [("0", .int 7), ("1", .int 8), ("2", .int 9), ("$esz", .int 1)] }
private def tB : Obj :=
  { cls := "<local>", fields := [("0", .int 1), ("1", .int 2), ("$esz", .int 4)] }
private def tS : Obj := { cls := "<local>", fields := [("x", .int 0), ("y", .int 0)] }
private def tH : Heap := [tA, tB, tS]

private def isB (r : EResult) (b : Bool) : Bool :=
  match r with | .val (.bool c) => c == b | _ => false
private def isHole (r : EResult) (l : String) : Bool :=
  match r with | .hole m => m == l | _ => false
private def isIdx (r : EResult) (blk : Ref) (i : Int) : Bool :=
  match r with | .val (.iref q (.idx j)) => q == blk && j == i | _ => false
private def isInt (r : EResult) (i : Int) : Bool :=
  match r with | .val (.int j) => j == i | _ => false

-- Extent and element size are read off the block.
example : tH.extent 0 = 3 := by decide
example : tH.extent 1 = 2 := by decide
example : tH.extent 2 = 0 := by decide
example : tH.elemSize 0 = some 1 := by decide
example : tH.elemSize 2 = none := by decide
example : tH.idxPos 0 3 = .onePast := by decide
example : tH.idxPos 0 4 = .outside := by decide
example : tH.idxPos 0 (-1) = .outside := by decide

-- Same block: ordering and equality compare offsets, one-past-the-end included.
example : isB (applyPtrOp tH "<"  0 (.iref 0 (.idx 1)) (.iref 0 (.idx 3))) true  := by decide
example : isB (applyPtrOp tH ">=" 0 (.iref 0 (.idx 1)) (.iref 0 (.idx 3))) false := by decide
example : isB (applyPtrOp tH "==" 0 (.iref 0 (.idx 2)) (.iref 0 (.idx 2))) true  := by decide
-- ... but not two past it: forming that pointer was undefined behaviour.
example : isHole (applyPtrOp tH "<" 0 (.iref 0 (.idx 1)) (.iref 0 (.idx 4))) "ub:ptr-out-of-bounds" := by decide
-- Different blocks: ordering is undefined.
example : isHole (applyPtrOp tH "<" 0 (.iref 0 (.idx 0)) (.iref 1 (.idx 0)))
    "ub:ptr-compare-cross-object" := by decide
-- Different blocks: equality is false while both point at elements ...
example : isB (applyPtrOp tH "==" 0 (.iref 0 (.idx 0)) (.iref 1 (.idx 1))) false := by decide
example : isB (applyPtrOp tH "!=" 0 (.iref 0 (.idx 0)) (.iref 1 (.idx 1))) true  := by decide
-- ... and UNSPECIFIED when one is one past the end (it may equal the next object's start).
example : isHole (applyPtrOp tH "==" 0 (.iref 0 (.idx 3)) (.iref 1 (.idx 0)))
    "ptr:eq-one-past-unspecified" := by decide
example : isHole (applyPtrOp tH "==" 0 (.iref 0 (.idx 3)) (.ref 2))
    "ptr:eq-one-past-unspecified" := by decide
-- Null: equal to null, unequal to every object pointer, unordered.
example : isB (applyPtrOp tH "==" 0 .unit (.int 0)) true := by decide
example : isB (applyPtrOp tH "!=" 0 (.iref 0 (.idx 3)) .unit) true := by decide
example : isB (applyPtrOp tH "==" 0 (.str "") .unit) false := by decide
example : isHole (applyPtrOp tH "<" 0 .unit (.iref 0 (.idx 0))) "ub:ptr-order-null" := by decide
-- Struct members: equality by member, no order.
example : isB (applyPtrOp tH "==" 0 (.iref 2 (.fld "x")) (.iref 2 (.fld "y"))) false := by decide
example : isHole (applyPtrOp tH "<" 0 (.iref 2 (.fld "x")) (.iref 2 (.fld "y"))) "ptr:member-order" := by decide
-- A member whose value is a nested box: `&s.arr` and `s.arr` are one address, two spellings.
private def tN : Heap := [tA, { cls := "<local>", fields := [("arr", .ref 0)] }]
example : isHole (applyPtrOp tN "==" 0 (.iref 1 (.fld "arr")) (.iref 0 (.idx 0)))
    "ptr:member-box-alias" := by decide
-- A block marked as a member box never compares unequal to another block by default.
private def tM : Heap := [{ tA with fields := tA.fields ++ [("$member", .bool true)] }, tB]
example : isHole (applyPtrOp tM "==" 0 (.ref 0) (.ref 1)) "ptr:member-box-alias" := by decide
example : isHole (applyPtrOp tM "==" 0 (.iref 0 (.idx 1)) (.iref 1 (.idx 0)))
    "ptr:member-box-alias" := by decide
-- Strings have no address.
example : isHole (applyPtrOp tH "==" 0 (.str "a") (.str "a")) "str:pointer-equality-not-modelled" := by decide
-- Arithmetic: element-stepped within the array, one-past-the-end allowed, stride checked.
example : isIdx (applyPtrOp tH "+" 1 (.iref 0 (.idx 1)) (.int 2)) 0 3 := by decide
example : isHole (applyPtrOp tH "+" 1 (.iref 0 (.idx 1)) (.int 3)) "ub:ptr-arith-out-of-bounds" := by decide
example : isHole (applyPtrOp tH "-" 1 (.iref 0 (.idx 1)) (.int 2)) "ub:ptr-arith-out-of-bounds" := by decide
example : isHole (applyPtrOp tH "+" 4 (.iref 0 (.idx 0)) (.int 1)) "ptr:stride-mismatch" := by decide
example : isIdx (applyPtrOp tH "+" 4 (.iref 1 (.idx 0)) (.int 1)) 1 1 := by decide
example : isHole (applyPtrOp tH "+" 1 (.iref 2 (.fld "x")) (.int 1)) "iref:arith-on-field" := by decide
example : isHole (applyPtrOp tH "+" 1 .unit (.int 0)) "ub:ptr-arith-null" := by decide
-- Difference: same block, same stride.
example : isInt (applyPtrOp tH "diff" 1 (.iref 0 (.idx 3)) (.iref 0 (.idx 1))) 2 := by decide
example : isHole (applyPtrOp tH "diff" 1 (.iref 0 (.idx 0)) (.iref 1 (.idx 0)))
    "ub:ptr-diff-cross-object" := by decide
-- The string model: forward only, never past the terminator.
example : (match applyPtrOp tH "+" 1 (.str "abc") (.int 1) with
           | .val (.str s) => s == "bc" | _ => false) = true := by decide
example : isHole (applyPtrOp tH "+" 1 (.str "abc") (.int 4)) "ptr:str-past-terminator" := by decide
example : isHole (applyPtrOp tH "-" 1 (.str "abc") (.int 1)) "ptr:str-before-start" := by decide
-- Casts: pointers pass, non-zero integers do not.
example : (match ptrCast (.iref 0 (.idx 2)) with | .val (.iref 0 (.idx 2)) => true | _ => false) = true := by decide
example : (match ptrCast (.int 8) with | .hole _ => true | _ => false) = true := by decide

end Autoform.Core
