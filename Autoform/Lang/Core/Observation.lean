import Autoform.Lang.Core.Semantics

/-! Native observations describe a rooted heap graph, not allocator addresses.
Input objects keep their addresses; freshly reachable objects are related bijectively.
Unreachable interpreter temporaries, globals outside the roots, instance-dictionary
insertion order, immutable-value identity, and internal mutation versions are outside
this observation. Dictionary payload order, aliases and cycles are inside it.
The checker is total and kernel reducible. Exhausting its budget is never agreement. -/
namespace Autoform.Core

structure HeapObservation where
  heap : Heap
  roots : List Ref
  budget : Nat := 10000
  deriving Repr, Inhabited

namespace HeapObservation

private inductive Task where
  | value : Val → Val → Task
  | object : Ref → Ref → Task

private def values (xs ys : List Val) : Option (List Task) :=
  if xs.length == ys.length then some ((xs.zip ys).map (fun (x, y) => .value x y))
  else none

private def pairs (xs ys : List (Val × Val)) : Option (List Task) :=
  if xs.length == ys.length then
    some ((xs.zip ys).flatMap (fun ((k, v), (l, w)) => [.value k l, .value v w]))
  else none

/- `Heap.setField` prepends a binding and field lookup reads the first one.
Older bindings are interpreter storage, not extra Python attributes. -/
private def visibleFields : List (String × Val) → List String → List (String × Val)
  | [], _ => []
  | (name, value) :: rest, seen =>
    if seen.contains name then visibleFields rest seen
    else (name, value) :: visibleFields rest (name :: seen)

private def fields (xs stored : List (String × Val)) : Option (List Task) := do
  let ys := visibleFields stored []
  if xs.length != ys.length then none else
  xs.mapM fun (name, v) => do
    if (xs.filter (·.1 == name)).length != 1 then none else
    match ys.filter (·.1 == name) with
    | [(_, w)] => some (.value v w)
    | _ => none

private def payload (x y : Payload) : Option (List Task) :=
  match x, y with
  | .none, .none => some []
  | .list xs, .list ys | .tuple xs, .tuple ys => values xs ys
  | .dict xs, .dict ys => pairs xs ys
  | _, _ => none

private def scalar (x y : Val) : Option (List Task) :=
  match x, y with
  | .int a, .int b => if a == b then some [] else none
  | .bool a, .bool b => if a == b then some [] else none
  | .str a, .str b => if a == b then some [] else none
  | .float a, .float b => if a = b then some [] else none
  | .unit, .unit => some []
  | .fn a, .fn b | .fn a, .clos b [] => if a == b then some [] else none
  | .list xs, .list ys | .tuple xs, .tuple ys => values xs ys
  | .dict xs, .dict ys => pairs xs ys
  | _, _ => none

/-- The address relation is injective in both directions. A separate visited set
ensures preassigned input addresses still have their contents checked once. -/
private def check (expected actual : Heap) :
    Nat → List Task → List (Ref × Ref) → List Ref → Option Bool
  | _, [], _, _ => some true
  | 0, _ :: _, _, _ => none
  | n + 1, task :: rest, mapping, visited =>
    match task with
    | .value (.ref e) (.ref a) =>
      match mapping.find? (·.1 == e) with
      | some (_, assigned) =>
        if assigned != a then some false
        else check expected actual n (.object e a :: rest) mapping visited
      | none =>
        if mapping.any (·.2 == a) then some false
        else check expected actual n (.object e a :: rest) ((e, a) :: mapping) visited
    | .value e a =>
      match scalar e a with
      | none => some false
      | some tasks => check expected actual n (tasks ++ rest) mapping visited
    | .object e a =>
      if visited.contains e then check expected actual n rest mapping visited else
      match expected.get e, actual.get a with
      | some x, some y =>
        if x.cls != y.cls || !x.captured.isEmpty || !y.captured.isEmpty then some false else
        match fields x.fields y.fields, payload x.payload y.payload with
        | some fs, some ps => check expected actual n (fs ++ ps ++ rest) mapping (e :: visited)
        | _, _ => some false
      | _, _ => some false

/-- Compare the recorded result and every input-rooted object's final contents.
`none` means comparison budget exhaustion, `some false` means a disagreement. -/
def compare (o : HeapObservation) (actual : Heap) (expected result : EResult) : Option Bool :=
  let tasks := o.roots.map (fun r => Task.object r r)
  let mapping := o.roots.map (fun r => (r, r))
  match expected, result with
  | .val e, .val a | .exn e, .exn a =>
      check o.heap actual o.budget (.value e a :: tasks) mapping []
  | _, _ => some false

end HeapObservation
end Autoform.Core
