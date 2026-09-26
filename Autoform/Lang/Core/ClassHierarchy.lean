import Std

/-!
Python class lookup needs an ordered namespace, not a search for any same-named
method. Qualified names identify declarations. Unresolved external bases require a namespace contract; an inconsistent
hierarchy has no usable prefix. C3 follows https://docs.python.org/3/howto/mro.html.
-/

namespace Autoform.Core

/-- A declaration in a class namespace. Unknown values still shadow base members. -/
inductive ClassAttribute where
  | method : String → ClassAttribute
  | property : String → ClassAttribute
  | stored : String → ClassAttribute
  | slot : String → ClassAttribute
  | opaque : String → ClassAttribute
  deriving Repr, Inhabited, BEq

/-- Source-recovered class metadata. Names and base names are qualified identities;
short names are aliases only when exactly one declaration owns that spelling. -/
structure ClassDecl where
  name : String
  shortName : String
  bases : List String := []
  attributes : List (String × ClassAttribute) := []
  /-- None creates an instance dictionary; some [] explicitly suppresses it.
  Names are already private-name mangled. Special layout names remain in this list. -/
  slots : Option (List String) := none
  /-- Dynamic class bodies, metaclasses or decorators may alter the whole namespace. -/
  definitionBarrier : Option String := none
  /-- Local base captures require class-object state before inheritance is faithful. -/
  inheritanceBarrier : Option String := none
  deriving Repr, Inhabited, BEq

/-- Complete linearization, a safe prefix ending at an unknown boundary, or a
rejected hierarchy. A rejected hierarchy must never expose even its own namespace. -/
inductive ClassOrder where
  | complete : List String → ClassOrder
  | incomplete : List String → String → ClassOrder
  | invalid : String → ClassOrder
  deriving Repr, Inhabited, BEq

inductive ClassLookup where
  | found : String → ClassAttribute → ClassLookup
  | absent : ClassLookup
  | blocked : String → ClassLookup
  deriving Repr, Inhabited, BEq

namespace ClassHierarchy

/-- The first C3 head absent from every remaining tail. -/
def goodHead (sequences : List (List String)) : Option String :=
  (sequences.filterMap (fun sequence => sequence.head?)).find? fun candidate =>
    !sequences.any (fun sequence => sequence.tail.contains candidate)

/-- Remove a selected head from every sequence that starts with it. -/
def removeHead (name : String) (sequences : List (List String)) : List (List String) :=
  sequences.map fun sequence =>
    match sequence with
    | head :: tail => if head == name then tail else sequence
    | [] => []

/-- Bounded structural recursion makes both native and kernel computation total.
The public merger supplies the sum of input lengths, enough for every removal. -/
def mergeAt : Nat → List (List String) → Option (List String)
  | 0, sequences => if sequences.all List.isEmpty then some [] else none
  | fuel + 1, sequences =>
      if sequences.all List.isEmpty then some []
      else
        match goodHead sequences with
        | none => none
        | some name => (mergeAt fuel (removeHead name sequences)).map (name :: ·)

def merge (sequences : List (List String)) : Option (List String) :=
  mergeAt (sequences.foldl (fun total sequence => total + sequence.length) 0) sequences

def ownDataSlots (declarations : List ClassDecl) (name : String) : Bool :=
  ((declarations.find? (·.name == name)).bind (·.slots)).getD [] |>.any
    (fun name => name != "__dict__" && name != "__weakref__")

def allowsDictIn (declarations : List ClassDecl) (order : List String) : Bool :=
  order.any fun name =>
    match declarations.find? (·.name == name) with
    | none => false
    | some declaration => declaration.slots.isNone ||
        (declaration.slots.getD []).contains "__dict__"

def allowsWeakrefIn (declarations : List ClassDecl) (order : List String) : Bool :=
  order.any fun name =>
    match declarations.find? (·.name == name) with
    | none => false
    | some declaration => declaration.slots.isNone ||
        (declaration.slots.getD []).contains "__weakref__"

/-- Each parent's first nonempty slot layout must lie on one inheritance chain.
An empty-slot mixin contributes no layout. Parent orders have already been checked. -/
def layoutGap (declarations : List ClassDecl) (declaration : ClassDecl)
    (sequences : List (List String)) (order : List String) : Option String :=
  let providers := sequences.filterMap (fun names => names.find? (ownDataSlots declarations))
  if !providers.isEmpty && !sequences.any (fun names => providers.all names.contains) then
    some "class-layout:incompatible-slotted-bases"
  else if (declaration.slots.getD []).contains "__dict__" && allowsDictIn declarations order then
    some "class-layout:duplicate-dict-slot"
  else if (declaration.slots.getD []).contains "__weakref__" && allowsWeakrefIn declarations order then
    some "class-layout:duplicate-weakref-slot"
  else none

/-- Resolve every parent before using a source class namespace. An unresolved base
may supply a metaclass that changes the derived namespace, so it is not safe to
expose even an own member without a contract. A local-capture boundary can preserve
an own namespace only after all parent orders are known. -/
def linearizeAt : Nat → List ClassDecl → String → ClassOrder
  | 0, _, _ => .invalid "class-hierarchy:cycle-or-depth"
  | fuel + 1, declarations, name =>
      if name == "__builtin.object" then .complete [name]
      else
        match declarations.filter (·.name == name) with
        | [declaration] =>
          match declaration.definitionBarrier with
          | some reason => .incomplete [] reason
          | none =>
            if declaration.bases.eraseDups.length != declaration.bases.length then
              .invalid "class-hierarchy:duplicate-base"
            else
              let parents := if declaration.bases.isEmpty then ["__builtin.object"]
                else declaration.bases
              let orders := parents.map (linearizeAt fuel declarations)
              match orders.findSome? (fun order =>
                  match order with | .invalid reason => some reason | _ => none) with
              | some reason => .invalid reason
              | none =>
                match orders.findSome? (fun order =>
                    match order with | .incomplete _ reason => some reason | _ => none) with
                | some reason => .incomplete [] reason
                | none =>
                  let sequences := orders.map fun order =>
                    match order with | .complete names => names | _ => []
                  match merge (sequences ++ [parents]) with
                  | none => .invalid "class-hierarchy:inconsistent-mro"
                  | some order =>
                    match layoutGap declarations declaration sequences order with
                    | some reason => .invalid reason
                    | none =>
                      match declaration.inheritanceBarrier with
                      | some reason => .incomplete [name] reason
                      | none => .complete (name :: order)
        | [] => .incomplete [] ("class-hierarchy:unresolved-base:" ++ name)
        | _ => .invalid ("class-hierarchy:duplicate-identity:" ++ name)

def linearize (declarations : List ClassDecl) (name : String) : ClassOrder :=
  linearizeAt (declarations.length + 1) declarations name

/-- Legacy instance names can be used only when the class declaration is unique. -/
def canonicalName (declarations : List ClassDecl) (name : String) : Option String :=
  match declarations.filter (·.name == name) with
  | [declaration] => some declaration.name
  | [] =>
      match declarations.filter (·.shortName == name) with
      | [declaration] => some declaration.name
      | _ => none
  | _ => none

def allowsDict (declarations : List ClassDecl) (name : String) : Bool :=
  match canonicalName declarations name with
  | none => false
  | some owner =>
    match linearize declarations owner with
    | .complete order => allowsDictIn declarations order
    | _ => false

/-- Attribute names provided by the builtin root still need their descriptor or
runtime models. Their presence must not be confused with an ordinary missing key. -/
def objectAttributes : List String :=
  ["__class__", "__dict__", "__weakref__", "__doc__", "__repr__", "__str__",
   "__hash__", "__new__", "__init__", "__getattribute__", "__setattr__", "__delattr__",
   "__sizeof__", "__dir__", "__reduce__", "__reduce_ex__", "__format__",
   "__init_subclass__", "__subclasshook__", "__getstate__", "__eq__", "__ne__",
   "__lt__", "__le__", "__gt__", "__ge__"]

def ownAttribute (declarations : List ClassDecl) (owner attr : String) :
    Option ClassAttribute :=
  if owner == "__builtin.object" then
    if objectAttributes.contains attr then some (.opaque ("class-attribute:object:" ++ attr))
    else none
  else
    (declarations.find? (·.name == owner)).bind fun declaration =>
      (declaration.attributes.find? (·.1 == attr)).map Prod.snd

def lookupIn (declarations : List ClassDecl) (order : List String) (attr : String) :
    Option (String × ClassAttribute) :=
  order.findSome? fun owner => (ownAttribute declarations owner attr).map (owner, ·)

/-- Select the first class namespace containing the name, before applying any
descriptor precedence or consulting an instance dictionary. -/
def lookup (declarations : List ClassDecl) (name attr : String) : ClassLookup :=
  match canonicalName declarations name with
  | none => .blocked ("class-hierarchy:unresolved-identity:" ++ name)
  | some owner =>
    match linearize declarations owner with
    | .invalid reason => .blocked reason
    | .complete order =>
        match lookupIn declarations order attr with
        | some (declaringClass, member) => .found declaringClass member
        | none => .absent
    | .incomplete known reason =>
        match lookupIn declarations known attr with
        | some (declaringClass, member) => .found declaringClass member
        | none => .blocked reason

end ClassHierarchy
end Autoform.Core
