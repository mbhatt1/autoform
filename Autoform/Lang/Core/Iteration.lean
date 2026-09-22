import Autoform.Lang.Core.Stdlib

/-!
# Python iterator objects

Iterator positions and exhaustion are heap state. Container iterators retain their
source reference, so list mutations remain visible. The protocol methods below are
ordinary Core functions: sequence fallback and callable/sentinel iteration therefore
run user code through the same fuel-bounded interpreter as every other call.

References: Python library/functions.html#iter and library/stdtypes.html#iterator-types.
Dictionary replacement of values is supported. A changed key layout at unchanged size
remains an explicit hole because Core does not represent CPython's dictionary slots.
-/

namespace Autoform.Core.Iteration

def dataClass : String := "<builtin-container-iterator>"
def sequenceClass : String := "<builtin-sequence-iterator>"
def callableClass : String := "<builtin-callable-iterator>"
def factoryClass : String := "<builtin-sequence-iterator-factory>"

def iteratorClass (cls : String) : Bool :=
  cls == dataClass || cls == sequenceClass || cls == callableClass

/-- Missing method declarations do not establish absent inherited/metaclass slots.
Plain builtin values are known not to be iterators; ordinary objects require more
class information before rejecting an __iter__ result with TypeError. -/
def unknownResultProtocol (h : Heap) : Val → Bool
  | .ref r => match h.payload r with | .none => true | _ => false
  | .bobj _ _ | .clsClos _ _ => true
  | .fn name => name.endsWith "<meta>"
  | _ => false

def allocate (h : Heap) (cls : String) (source : Val) (extra : List (String × Val) := []) :
    Heap × EResult :=
  let (h', r) := h.alloc { cls := cls, fields :=
    [("<source>", source), ("<index>", .int 0), ("<closed>", .bool false)] ++ extra }
  (h', .val (.ref r))

def dictionaryObject (source : Val) (kvs : List (Val × Val)) : Obj :=
  { cls := dataClass, fields :=
    [("<source>", source), ("<index>", .int 0), ("<closed>", .bool false),
     ("<keys>", .tuple (kvs.map Prod.fst)), ("<size>", .int kvs.length),
     ("<size-error>", .bool false)] }

def sequenceObject (source : Val) : Obj :=
  { cls := sequenceClass, fields :=
    [("<source>", source), ("<index>", .int 0), ("<closed>", .bool false)] }

def newData (h : Heap) (source : Val) : Option (Heap × EResult) :=
  match source.unbox h with
  | .list _ | .tuple _ | .str _ => some (allocate h dataClass source)
  | .dict kvs =>
      let (h', r) := h.alloc (dictionaryObject source kvs)
      some (h', .val (.ref r))
  | .ref _ | .bobj _ _ | .clsClos _ _ => none
  | _ => some (h, .exn (.str "TypeError"))

def stop (h : Heap) (r : Ref) : Heap × EResult :=
  (h.setField r "<closed>" (.bool true), .exn (.str "StopIteration"))

def takeAt (h : Heap) (r : Ref) (i : Nat) (values : List Val) : Heap × EResult :=
  match values[i]? with
  | none => stop h r
  | some value => (h.setField r "<index>" (.int (i + 1)), .val value)

def dataNext (h : Heap) (r : Ref) : Heap × EResult :=
  if h.getField r "<closed>" == .bool true then (h, .exn (.str "StopIteration"))
  else
  match h.getField r "<index>" with
  | .int index =>
    if index < 0 then (h, .hole "iterator:invalid-index") else
    match (h.getField r "<source>").unbox h with
    | .list values | .tuple values => takeAt h r index.toNat values
    | .str value => takeAt h r index.toNat (value.toList.map (fun c => .str c.toString))
    | .dict kvs =>
      if h.getField r "<size-error>" == .bool true ||
          h.getField r "<size>" != .int kvs.length then
        (h.setField r "<size-error>" (.bool true), .exn (.str "RuntimeError"))
      else if h.getField r "<keys>" != .tuple (kvs.map Prod.fst) then
        (h, .hole "iterator:dict-keys-changed")
      else takeAt h r index.toNat (kvs.map Prod.fst)
    | _ => (h, .hole "iterator:source-kind-changed")
  | _ => (h, .hole "iterator:invalid-index")

/-- Stateful builtins are kept separate from `Stdlib.builtin`'s heap-preserving models. -/
def freeNames : List String :=
  ["iter", "next", "<iterator-next>", "<sequence-iter>", "<iterator-identical>"]

def knowsFree (d : Dialect) (name : String) : Bool :=
  d == .python && freeNames.contains name

/-- Identity is only a shortcut for sentinel equality. For ints and strings the
equality result is unaffected by identity, so unknown interning can skip the shortcut.
Unrepresented identity for other values remains a hole, notably float NaNs. -/
def sentinelIdentity (a b : Val) : EResult :=
  match Val.identical a b with
  | some same => .val (.bool same)
  | none => match a, b with
    | .int _, .int _ | .str _, .str _ => .val (.bool false)
    | .float x, .float y =>
        if x.isNaN && y.isNaN then .hole "iterator:sentinel-identity" else .val (.bool false)
    | _, _ => .hole "iterator:sentinel-identity"

def builtin (d : Dialect) (h : Heap) (name : String) (args : List Val) :
    Option (Heap × EResult) :=
  if !knowsFree d name then none else
  match name, args with
  | "iter", [source] => newData h source
  | "iter", [callable, sentinel] =>
    match callable with
    | .fn _ | .clos _ _ => some (allocate h callableClass callable [("<sentinel>", sentinel)])
    | .ref _ | .bobj _ _ | .clsClos _ _ => none
    | _ => some (h, .exn (.str "TypeError"))
  | "<sequence-iter>", [source] => some (allocate h sequenceClass source)
  | "<iterator-identical>", [a, b] => some (h, sentinelIdentity a b)
  | "<iterator-next>", [.ref r] =>
    match h.get r with
    | some object => if object.cls == dataClass then some (dataNext h r) else none
    | none => some (h, .hole "iterator:dangling-reference")
  -- Valid `next` calls dispatch through __next__ before reaching this fallback.
  | _, _ => some (h, .exn (.str "TypeError"))

/-- An explicit container.__iter__() retains the original reference too. -/
def containerMethod (d : Dialect) (h : Heap) (receiver : Val) (name : String)
    (args : List Val) (keywords : List (String × Val)) : Option (Heap × EResult) :=
  if d == .python && name == "__iter__" && (receiver.unbox h).iterable.isSome then
    if args.isEmpty && keywords.isEmpty then newData h receiver
    else some (h, .exn (.str "TypeError"))
  else none

theorem knowsFree_complete :
    freeNames.all (fun name => (builtin .python [] name []).isSome) = true := by decide

theorem builtin_none_of_not_knowsFree {d : Dialect} {h : Heap} {name : String}
    {args : List Val} (unknown : knowsFree d name = false) : builtin d h name args = none := by
  simp [builtin, unknown]

private def self : Expr := .name "self"
private def field (name : String) : Expr := .field self name
private def close : Stmt := .setField self "<closed>" (.lit (.bool true))
private def raiseName (name : String) : Stmt :=
  .raise (.unop ("py:exception:" ++ name) (.tupleE []))
private def stopBody : Stmt := .seq close (raiseName "StopIteration")

/-- Unknown user exception ancestry must not be guessed at by a synthetic handler. -/
private def propagate : Stmt :=
  .ifte (.inOp false (.name "<caught>") (.tupleE (Stdlib.excNames.map (fun n => .lit (.str n)))))
    (.raise (.name "<caught>")) (.hole "iterator:exception-hierarchy")

def sequenceNextBody : Stmt :=
  .ifte (field "<closed>") (raiseName "StopIteration")
    (.seq
      (.tryCatch (.assign "<value>" (.index (field "<source>") (field "<index>"))) "<caught>"
        (.ifte (.binop "||"
          (.binop "==" (.name "<caught>") (.lit (.str "IndexError")))
          (.binop "==" (.name "<caught>") (.lit (.str "StopIteration")))) stopBody propagate))
      (.seq (.setField self "<index>" (.binop "+" (field "<index>") (.lit (.int 1))))
        (.ret (.name "<value>"))))

def callableNextBody : Stmt :=
  .ifte (field "<closed>") (raiseName "StopIteration")
    (.seq
      (.tryCatch (.assign "<value>" (.callValue (field "<source>") [])) "<caught>"
        (.ifte (.binop "==" (.name "<caught>") (.lit (.str "StopIteration"))) stopBody propagate))
      -- CPython's calliter_iternext compares sentinel first and uses identity
      -- before rich equality; a callback can also exhaust this iterator reentrantly.
      (.ifte (field "<closed>") (raiseName "StopIteration")
        (.ifte (.call "<iterator-identical>" [field "<sentinel>", .name "<value>"]) stopBody
          (.ifte (.call "bool" [.binop "==" (field "<sentinel>") (.name "<value>")]) stopBody
            (.ret (.name "<value>"))))))

private def method (cls name : String) (body : Stmt) : Func :=
  { name := "<runtime>." ++ cls ++ "." ++ name, params := [], body := body,
    pythonSignature := some { isMethod := some true } }

/-- Reserved classes cannot be declared in Python source. Their methods do not enter
the ordinary function table or interfere with suffix resolution of source names. -/
def resolveMethod (cls name : String) : Option Func :=
  if cls == factoryClass && name == "__iter__" then
    some (method cls name (.ret (.call "<sequence-iter>" [self])))
  else if iteratorClass cls && name == "__iter__" then
    some (method cls name (.ret self))
  else if name == "__next__" then
    if cls == dataClass then some (method cls name (.ret (.call "<iterator-next>" [self])))
    else if cls == sequenceClass then some (method cls name sequenceNextBody)
    else if cls == callableClass then some (method cls name callableNextBody)
    else none
  else none

private theorem allocate_ne_exn {h : Heap} {cls : String} {source : Val}
    {extra : List (String × Val)} {v : Val} :
    (allocate h cls source extra).2 = .exn v → False := by
  simp [allocate, Heap.alloc]

private theorem sentinelIdentity_ne_exn {a b v : Val} :
    sentinelIdentity a b = .exn v → False := by
  unfold sentinelIdentity
  repeat' split
  all_goals intro impossible; cases impossible

private theorem takeAt_excSafe (h : Heap) (r i : Nat) (values : List Val) {v : Val} :
    (takeAt h r i values).2 = .exn v → Stdlib.ExcSafe v := by
  intro result
  unfold takeAt at result
  split at result
  · cases result; exact Stdlib.excSafe_str (by decide)
  · cases result

theorem dataNext_excSafe (h : Heap) (r : Ref) {v : Val} :
    (dataNext h r).2 = .exn v → Stdlib.ExcSafe v := by
  intro result
  unfold dataNext at result
  repeat' split at result
  all_goals first
    | exact takeAt_excSafe _ _ _ _ result
    | (cases result; exact Stdlib.excSafe_str (by decide))
    | cases result

theorem newData_excSafe (h : Heap) (source : Val) {h' : Heap} {v : Val} :
    newData h source = some (h', .exn v) → Stdlib.ExcSafe v := by
  intro result
  unfold newData at result
  split at result
  all_goals first
    | exact (allocate_ne_exn (congrArg Prod.snd (Option.some.inj result))).elim
    | (cases result; exact Stdlib.excSafe_str (by decide))
    | cases result

theorem builtin_excSafe (d : Dialect) (h : Heap) (name : String) (args : List Val)
    {h' : Heap} {v : Val} :
    builtin d h name args = some (h', .exn v) → Stdlib.ExcSafe v := by
  intro result
  unfold builtin at result
  repeat' split at result
  all_goals first
    | exact newData_excSafe _ _ result
    | exact (sentinelIdentity_ne_exn (congrArg Prod.snd (Option.some.inj result))).elim
    | exact dataNext_excSafe _ _ (congrArg Prod.snd (Option.some.inj result))
    | exact (allocate_ne_exn (congrArg Prod.snd (Option.some.inj result))).elim
    | (cases result; exact Stdlib.excSafe_str (by decide))
    | cases result

theorem containerMethod_excSafe (d : Dialect) (h : Heap) (receiver : Val) (name : String)
    (args : List Val) (keywords : List (String × Val)) {h' : Heap} {v : Val} :
    containerMethod d h receiver name args keywords = some (h', .exn v) → Stdlib.ExcSafe v := by
  intro result
  unfold containerMethod at result
  repeat' split at result
  all_goals first
    | exact newData_excSafe _ _ result
    | (cases result; exact Stdlib.excSafe_str (by decide))
    | cases result

end Autoform.Core.Iteration
