import Autoform.Lang.Core.Stdlib

/-!
# Boxed containers: the heap-free half

`docs/boxed-containers.md`, steps 3 and 4, for **Python**. A list or dict display
evaluates to a `Val.ref` whose heap object carries the contents as its `Payload`
(`Expr.boxContainer`). This file holds the pieces of that design that do not need the
interpreter's mutual recursion -- what a write does to a payload, what a membership test or
a builtin is allowed to see -- so that `Semantics.lean` changes only at its call sites.

## The rule

After a receiver has been evaluated to `.ref r`, mutation is `Heap.setPayload r`, and
nothing is ever written back through an expression. That is what makes
`t = self.d; t.pop(k)` (the CPG's own desugaring) update `self.d`: both names hold the
same reference.

## What a boxed container may be handed to

`Heap.view` (in `Syntax.lean`) replaces a boxed reference by its contents ONE level deep.
That is exactly right for a consumer that copies or counts elements -- `len`, `list(x)`,
iteration, `xs + ys`, `f(*xs)` -- because the elements keep their identity. It is NOT
right for a consumer that compares or tests elements with the heap-free `Val.beq` /
`Val.truthy`: `Val.beq` compares two references by ADDRESS, and `[1] == [1]` is `True`.
So every such consumer is guarded by `Heap.hasBoxed`, and refuses (a hole) rather than
answers when a boxed reference is reachable inside what it would compare.

## Deliberately not modelled (holes, not answers)

* `dict.keys()`/`values()`/`items()` on a BOXED dict. CPython returns a live view; a
  snapshot list would be silently stale after the next write, and a write is now possible.
* `list.count`/`index`/`remove` when an element or the argument is (or contains) a boxed
  container -- element equality would need `Val.eqPy`, which `Stdlib` does not take.
* Slice assignment and slice deletion (the exporter already holes them).
* Mutating a container while iterating it: the loop is run on a snapshot and the result
  is replaced by `forIn:container-mutated-during-iteration` if the object's `version`
  moved. Sound (CPython's list iterator would have seen the change; its dict iterator
  raises `RuntimeError`), but conservative: a loop that mutates and then returns before the
  next element is fetched would have agreed with CPython and is still refused.
-/

namespace Autoform.Core

/-- Python, and only Python, has boxed containers in Core. -/
def Dialect.isPython : Dialect → Bool
  | .python => true
  | _       => false

namespace Payload

/-- The payload as the value `Stdlib` speaks. `.none` has no container view. -/
def toVal : Payload → Option Val
  | .none     => Option.none
  | .list vs  => some (.list vs)
  | .dict kvs => some (.dict kvs)
  | .tuple vs => some (.tuple vs)

/-- The class name a boxed container is allocated with. -/
def clsName : Payload → String
  | .none    => "object"
  | .list _  => "list"
  | .dict _  => "dict"
  | .tuple _ => "tuple"

end Payload

/-- The payload a `Stdlib` mutating method's new receiver value becomes. Anything else is a
mismatch between `Stdlib` and this file and must not be stored. -/
def Val.toPayload : Val → Option Payload
  | .list vs  => some (.list vs)
  | .dict kvs => some (.dict kvs)
  | _         => none

namespace Heap

mutual
/-- Is a reference to a boxed container reachable inside `v`, through VALUE containers
only (references are not followed)? This is the guard for every heap-free consumer that
compares or tests elements: `Val.beq` would compare such a reference by address. -/
def hasBoxed (h : Heap) : Val → Bool
  | .ref r =>
      match h.payload r with
      | .none => false
      | _     => true
  | .list vs  => hasBoxedL h vs
  | .tuple vs => hasBoxedL h vs
  | .dict kvs => hasBoxedP h kvs
  | .bobj _ v => hasBoxed h v
  | _ => false
def hasBoxedL (h : Heap) : List Val → Bool
  | []      => false
  | v :: vs => hasBoxed h v || hasBoxedL h vs
def hasBoxedP (h : Heap) : List (Val × Val) → Bool
  | []           => false
  | (k, v) :: ps => hasBoxed h k || hasBoxed h v || hasBoxedP h ps
end

mutual
/-- Python's `TypeError: unhashable type`: a list or dict, boxed or not, or a tuple that
contains one. Instances of builtin-based classes are left alone (a `list` subclass may
define `__hash__`), as are plain objects (hashable by identity unless they say otherwise,
which is the existing `__eq__`/`__hash__` boundary). -/
def unhashable (h : Heap) : Val → Bool
  | .ref r =>
      match h.payload r with
      | .list _ => true
      | .dict _ => true
      | _       => false
  | .list _   => true
  | .dict _   => true
  | .tuple vs => unhashableL h vs
  | _ => false
def unhashableL (h : Heap) : List Val → Bool
  | []      => false
  | v :: vs => unhashable h v || unhashableL h vs
end

/-- Allocate a fresh boxed container for a `Val.list`/`Val.dict`; any other value is
returned as it is. Used for the results of builtins that construct a NEW container
(`list(x)`, `sorted(x)`, `dict(x)`, `xs.copy()`), each of which is a fresh object in
CPython.

A `Val.tuple` is the result shape of `<unpackEx>` (starred assignment, `a, *b, c = xs`),
whose starred slot is a NEW list in CPython (`b` is bound to a fresh list even when `xs` is
a tuple or a string). The tuple itself is an immutable value and stays one; each `list`/
`dict` value directly inside it is boxed. No other fresh-builtin returns a tuple, so this
case is reached only from there. -/
def boxFresh (h : Heap) (v : Val) : Heap × Val :=
  match v with
  | .list vs  => let (h', r) := h.alloc { cls := "list", fields := [], payload := .list vs }
                 (h', .ref r)
  | .dict kvs => let (h', r) := h.alloc { cls := "dict", fields := [], payload := .dict kvs }
                 (h', .ref r)
  | .tuple es =>
      let step : Heap × List Val → Val → Heap × List Val := fun (acc : Heap × List Val) e =>
        match e with
        | .list vs  => let (h', r) := acc.1.alloc { cls := "list", fields := [], payload := .list vs }
                       (h', acc.2 ++ [.ref r])
        | .dict kvs => let (h', r) := acc.1.alloc { cls := "dict", fields := [], payload := .dict kvs }
                       (h', acc.2 ++ [.ref r])
        | _         => (acc.1, acc.2 ++ [e])
      let (h', es') := es.foldl step (h, [])
      (h', .tuple es')
  | _ => (h, v)

end Heap

/-- Write a key the way CPython's dict does: a key already present (by `==`) keeps its
ORIGINAL key object and position and takes the new value; a new key goes to the end. That
is the insertion-order guarantee of CPython 3.7+, and it is why `d[1.0] = x` on a dict
holding `1` leaves the key `1`. -/
def dictStore : List (Val × Val) → Val → Val → List (Val × Val)
  | [],             k, v => [(k, v)]
  | (k', v') :: ps, k, v =>
      if Val.beq k' k then (k', v) :: ps else (k', v') :: dictStore ps k v

/-- `xs[i]` on a sequence. A NEGATIVE index counts from the end in Python (`xs[-1]` is the
last element). It used to be clamped by `Int.toNat` to `0`, so `[7, 8, 9][-1]` read `7`:
a silent wrong answer, reachable on every Python corpus. Outside Python a negative index
into a sequence value has no single defined meaning (C: undefined behaviour; JS:
`undefined`), so it is a hole there rather than a guess. Non-negative indices behave
exactly as before in every dialect. -/
def seqRead (d : Dialect) (vs : List Val) (i : Int) : EResult :=
  if i < 0 then
    if d.isPython then
      match Stdlib.seqIndex vs.length i with
      | some j => match vs[j]? with
                  | some v => .val v
                  | none   => .exn (.str "IndexError")
      | none   => .exn (.str "IndexError")
    else .hole "index:negative"
  else if _hh : i.toNat < vs.length then .val (vs[i.toNat])
  else .exn (.str "IndexError")

/-- What a subscript write or delete does to a payload, without the heap. -/
inductive PayloadOp where
  | ok   : Payload → PayloadOp
  | exn  : String → PayloadOp
  | hole : String → PayloadOp
  deriving Repr, Inhabited

/-- A Python integer index, if the value is one. `bool` is an `int` subclass in CPython,
so `xs[True]` is `xs[1]`. -/
def pyIndex : Val → Option Int
  | .int i  => some i
  | .bool b => some (if b then 1 else 0)
  | _       => none

/-- Index values CPython rejects outright with `TypeError` ("list indices must be integers
or slices"). Anything else that is not an integer -- a reference, which may define
`__index__` -- stays a hole. -/
def badSeqIndex : Val → Bool
  | .str _ | .unit | .float _ | .tuple _ | .list _ | .dict _ => true
  | _ => false

/-- `c[k] = x` on a boxed container's payload. -/
def payloadStore (h : Heap) (p : Payload) (k x : Val) : PayloadOp :=
  match p with
  | .list vs =>
      match pyIndex k with
      | some i =>
          match Stdlib.seqIndex vs.length i with
          | some j => .ok (.list (vs.set j x))
          | none   => .exn "IndexError"
      | none => if badSeqIndex k then .exn "TypeError" else .hole "setIndex:list:index-shape"
  | .dict kvs =>
      if h.unhashable k then .exn "TypeError" else .ok (.dict (dictStore kvs k x))
  | .tuple _ => .exn "TypeError"
  | .none    => .hole "setIndex:non-container"

/-- `del c[k]` on a boxed container's payload. -/
def payloadDelete (h : Heap) (p : Payload) (k : Val) : PayloadOp :=
  match p with
  | .list vs =>
      match pyIndex k with
      | some i =>
          match Stdlib.seqIndex vs.length i with
          | some j => .ok (.list (Stdlib.dropAt vs j))
          | none   => .exn "IndexError"
      | none => if badSeqIndex k then .exn "TypeError" else .hole "delIndex:list:index-shape"
  | .dict kvs =>
      if h.unhashable k then .exn "TypeError"
      else match Stdlib.dictGet kvs k with
           | some _ => .ok (.dict (Stdlib.dictDel kvs k))
           | none   => .exn "KeyError"
  | .tuple _ => .exn "TypeError"
  | .none    => .hole "delIndex:non-container"

/-- A subscript write or delete on something that is NOT a heap object. Under Python an
immutable value is a modelled `TypeError` ("'tuple' object does not support item
assignment"); an UNBOXED list or dict -- one that came from somewhere other than a display
(a `**kwargs` dict, a `dict.keys()` list) -- cannot be written through, because Core does not
know who else holds it, so that stays the original hole. -/
def valueSubscriptWrite (d : Dialect) (c : Val) (what : String) : EResult :=
  if !d.isPython then .hole s!"{what}:immutable-containers"
  else match c with
  | .tuple _ | .str _ | .int _ | .bool _ | .unit | .float _ => .exn (.str "TypeError")
  | _ => .hole s!"{what}:immutable-containers"

/-- Membership through the heap. A boxed container is seen through `Heap.view`; elements
of a list or tuple are compared with `Val.eqPy` (CPython: `x is e or x == e`), which is
what makes `[1] in [[1]]` true; dict membership is a hash lookup, so an unhashable probe is
`TypeError` under Python, and a hashable probe contains no boxed reference, so `Val.beq`
on keys is unchanged. `none` from the comparison is ignorance and becomes `outOfFuel`,
exactly as for `==`. -/
def valInH (d : Dialect) (h : Heap) (x c : Val) : EResult :=
  let mem : List Val → EResult := fun vs =>
    match vs.foldl (fun acc e => match acc with
                      | some false => Val.eqPy h (Val.eqFuel h) e x
                      | other      => other) (some false) with
    | some b => .val (.bool b)
    | none   => .outOfFuel
  match (h.view c).unbuiltin with
  | .list vs  => mem vs
  | .tuple vs => mem vs
  | .dict kvs =>
      if d.isPython && h.unhashable x then .exn (.str "TypeError")
      else .val (.bool (kvs.any (fun kv => Val.beq x kv.1)))
  | .str s    => match x with
                 | .str t => .val (.bool ((s.splitOn t).length > 1))
                 | _      => .hole "in:non-str-in-str"
  | _         => .hole "in:non-container"

/-- Builtins that consume an argument AS AN ITERABLE OR A SCALAR and never return the
argument object itself, so handing them the boxed container's contents is exact.
`dict` is handled separately (only a dict argument is seen through). -/
def viewedBuiltins : List String :=
  ["len", "list", "tuple", "sorted", "sum", "min", "max", "bool", "isinstance", "callable",
   "<unpackEx>"]

/-- Builtins whose result is a FRESH mutable container in CPython. `<unpackEx>` returns a
tuple whose starred slot is such a container (see `Heap.boxFresh`). -/
def freshBuiltins : List String := ["list", "dict", "sorted", "<unpackEx>"]

/-- The arguments a builtin call hands to `Stdlib.builtin`, seen through the heap where
that is exact (`viewedBuiltins`). Every other builtin receives the reference itself, which
`Stdlib` does not match, so it holes rather than answering about a container it cannot
see. -/
def builtinArgs (h : Heap) (f : String) (vs : List Val) : List Val :=
  if viewedBuiltins.contains f then vs.map h.view
  else if f == "dict" then vs.map (fun v => match h.view v with
                                            | .dict kvs => .dict kvs
                                            | _         => v)
  else vs

/-- `dict(pairs)` would key on `Val.beq`; a boxed reference inside the pairs is refused. -/
def builtinRefused (h : Heap) (f : String) (vs : List Val) : Bool :=
  f == "dict" && vs.any (fun v => match v with
                                  | .dict _ => false
                                  | _       => h.hasBoxed v)

/-- Methods whose answer depends on `Val.beq` between ELEMENTS (or element and argument). -/
def elementEqMethods : List String := ["count", "index", "remove"]

/-- Methods whose first argument is a dict KEY. -/
def keyMethods : List String := ["get", "pop", "setdefault"]

/-- A method call on a container VALUE or PAYLOAD that the heap-free `Stdlib` must not
answer: element equality across a boxed reference. `some label` is the hole. -/
def methodRefusal (h : Heap) (recv : Val) (m : String) (vs : List Val) : Option String :=
  if elementEqMethods.contains m && (h.hasBoxed recv || vs.any h.hasBoxed) then
    some s!"mcall:{m}:boxed-element-equality"
  else none

/-- A dict-key method called with an unhashable key: CPython's `TypeError`. -/
def methodKeyError (d : Dialect) (h : Heap) (recv : Val) (m : String) (vs : List Val) :
    Bool :=
  d.isPython && keyMethods.contains m &&
    (match recv, vs with
     | .dict _, k :: _ => h.unhashable k
     | _, _ => false)

/-- A method call on a BOXED container. `Stdlib.method` sees the payload; a mutating result
is written back with `Heap.setPayload` to the SAME reference, and never through the
receiver expression. -/
def boxedMethod (d : Dialect) (h : Heap) (r : Ref) (p : Payload) (m : String)
    (vs : List Val) : Heap × EResult :=
  match p.toVal with
  | none => (h, .hole s!"mcall:{m}:non-container")
  | some recv =>
    match methodRefusal h recv m vs with
    | some l => (h, .hole l)
    | none =>
    if methodKeyError d h recv m vs then (h, .exn (.str "TypeError"))
    else
    match recv, m with
    -- A live view, which a snapshot list would silently fail to be once the dict is
    -- written to again. See the module docstring.
    | .dict _, "keys" | .dict _, "values" | .dict _, "items" =>
        (h, .hole s!"mcall:dict.{m}:live-view-not-modelled")
    | _, _ =>
    -- `extend`/`update` consume their argument as an iterable / mapping.
    let vs' := if m == "extend" || m == "update" then vs.map h.view else vs
    match Stdlib.method d h recv m vs' with
    | some (h₁, .pure (.val res)) =>
        if m == "copy" then let (h₂, v) := h₁.boxFresh res; (h₂, .val v)
        else (h₁, .val res)
    | some (h₁, .pure res) => (h₁, res)
    | some (h₁, .mutating res nv) =>
        match nv.toPayload with
        | some p' => (h₁.setPayload r p', res)
        | none    => (h₁, .hole s!"mcall:{m}:payload-shape")
    | none => (h, .hole s!"mcall:{p.clsName}.{m}")

/-! ## Evidence

Each line pins one rule of the design against CPython's answer. -/

section Evidence

/-- A one-object heap holding the list `[1, 2, 3]` at ref 0. -/
private def hL : Heap := [{ cls := "list", fields := [], payload := .list [.int 1, .int 2, .int 3] }]
/-- A one-object heap holding the dict `{'a': 1}` at ref 0. -/
private def hD : Heap := [{ cls := "dict", fields := [], payload := .dict [(.str "a", .int 1)] }]

/-- `xs[-1] = 9` writes the LAST element. -/
example : payloadStore hL (.list [.int 1, .int 2, .int 3]) (.int (-1)) (.int 9)
    = .ok (.list [.int 1, .int 2, .int 9]) := rfl
/-- `xs[3] = 0` on a 3-element list is `IndexError`, and so is `xs[-4]`. -/
example : (match payloadStore hL (.list [.int 1, .int 2, .int 3]) (.int 3) (.int 0) with
           | .exn e => e | _ => "") = "IndexError" := rfl
example : (match payloadStore hL (.list [.int 1, .int 2, .int 3]) (.int (-4)) (.int 0) with
           | .exn e => e | _ => "") = "IndexError" := rfl
/-- `xs['a'] = 0` is `TypeError`. -/
example : (match payloadStore hL (.list [.int 1]) (.str "a") (.int 0) with
           | .exn e => e | _ => "") = "TypeError" := rfl
/-- A new dict key goes to the END; an existing one is replaced in place. -/
example : dictStore [(.str "a", .int 1), (.str "b", .int 2)] (.str "a") (.int 9)
    = [(.str "a", .int 9), (.str "b", .int 2)] := rfl
example : dictStore [(.str "a", .int 1)] (.str "c") (.int 3)
    = [(.str "a", .int 1), (.str "c", .int 3)] := rfl
/-- `del d['zz']` on a dict without it is `KeyError`. -/
example : (match payloadDelete hD (.dict [(.str "a", .int 1)]) (.str "zz") with
           | .exn e => e | _ => "") = "KeyError" := rfl
/-- A boxed list is unhashable: `d[[1]] = 0` is `TypeError`. -/
example : hL.unhashable (.ref 0) = true := rfl
example : hL.unhashable (.tuple [.int 1, .ref 0]) = true := rfl
example : hL.unhashable (.tuple [.int 1, .str "x"]) = false := rfl
/-- The view of a boxed list is its contents; the view of a plain value is itself. -/
example : hL.view (.ref 0) = .list [.int 1, .int 2, .int 3] := rfl
example : hL.view (.int 4) = .int 4 := rfl
/-- `2 in xs` sees through the box. -/
example : (match valInH .python hL (.int 2) (.ref 0) with
           | .val (.bool b) => b | _ => false) = true := rfl

end Evidence

end Autoform.Core
