import Autoform.Lang.Core.Semantics

/-!
# Structural equality for Core values — support for the NL autoformalizer

`deriving DecidableEq` does not apply to `Val` (its constructors nest `List Val` and
`List (Val × Val)`), so the natural-language pipeline could not state, let alone decide,
"this frozen heap literal IS what the module initializers produce". This file supplies
that equality, by the usual route: a structural Boolean test `Val.seq`, a proof that it
is sound and reflexive, and the `DecidableEq` instances that follow for `Val`, `Payload`,
`Obj` (hence `Heap`) and `EResult`.

This is **structural** identity of Lean terms, not Python `==`: `Val.beq` (the
interpreter's equality) compares floats by IEEE rules and is deliberately not used here.
Everything reduces in the kernel, so `decide +kernel` can evaluate these instances on
concrete terms (`Autoform/NL/<Module>.lean` relies on it to prove its frozen initial heap).
-/

namespace Autoform.Core

deriving instance DecidableEq for Sel

mutual
/-- Structural equality of values. -/
def Val.seq : Val → Val → Bool
  | .int a,  .int b  => a == b
  | .str a,  .str b  => a == b
  | .bool a, .bool b => a == b
  | .float a, .float b => decide (a = b)
  | .unit, .unit => true
  | .list a, .list b => Val.seqL a b
  | .tuple a, .tuple b => Val.seqL a b
  | .dict a, .dict b => Val.seqP a b
  | .ref a, .ref b => a == b
  | .iref a s, .iref b t => a == b && decide (s = t)
  | .fn a, .fn b => a == b
  | .clsClos a xs, .clsClos b ys => a == b && Val.seqE xs ys
  | .clos a xs, .clos b ys => a == b && Val.seqE xs ys
  | .bobj a v, .bobj b w => a == b && Val.seq v w
  | _, _ => false
/-- Structural equality of value lists. -/
def Val.seqL : List Val → List Val → Bool
  | [], [] => true
  | a :: as, b :: bs => Val.seq a b && Val.seqL as bs
  | _, _ => false
/-- Structural equality of association lists of values. -/
def Val.seqP : List (Val × Val) → List (Val × Val) → Bool
  | [], [] => true
  | (a, a') :: as, (b, b') :: bs => Val.seq a b && Val.seq a' b' && Val.seqP as bs
  | _, _ => false
/-- Structural equality of named bindings. -/
def Val.seqE : List (String × Val) → List (String × Val) → Bool
  | [], [] => true
  | (a, a') :: as, (b, b') :: bs => a == b && Val.seq a' b' && Val.seqE as bs
  | _, _ => false
end

mutual
theorem Val.seq_sound : ∀ a b : Val, Val.seq a b = true → a = b
  | .int _, b, h | .str _, b, h | .bool _, b, h | .float _, b, h | .unit, b, h
  | .ref _, b, h | .iref _ _, b, h | .fn _, b, h => by
      cases b <;> simp_all [Val.seq]
  | .list xs, b, h => by
      cases b <;> simp [Val.seq] at h
      case list ys => rw [Val.seqL_sound xs ys h]
  | .tuple xs, b, h => by
      cases b <;> simp [Val.seq] at h
      case tuple ys => rw [Val.seqL_sound xs ys h]
  | .dict xs, b, h => by
      cases b <;> simp [Val.seq] at h
      case dict ys => rw [Val.seqP_sound xs ys h]
  | .clsClos n xs, b, h => by
      cases b <;> simp [Val.seq] at h
      case clsClos m ys => rw [h.1, Val.seqE_sound xs ys h.2]
  | .clos n xs, b, h => by
      cases b <;> simp [Val.seq] at h
      case clos m ys => rw [h.1, Val.seqE_sound xs ys h.2]
  | .bobj n v, b, h => by
      cases b <;> simp [Val.seq] at h
      case bobj m w => rw [h.1, Val.seq_sound v w h.2]
theorem Val.seqL_sound : ∀ a b : List Val, Val.seqL a b = true → a = b
  | [], b, h => by cases b <;> simp_all [Val.seqL]
  | x :: xs, b, h => by
      cases b <;> simp [Val.seqL] at h
      case cons y ys => rw [Val.seq_sound x y h.1, Val.seqL_sound xs ys h.2]
theorem Val.seqP_sound : ∀ a b : List (Val × Val), Val.seqP a b = true → a = b
  | [], b, h => by cases b <;> simp_all [Val.seqP]
  | (_, _) :: _, [], h => by simp [Val.seqP] at h
  | (x, x') :: xs, (y, y') :: ys, h => by
      simp [Val.seqP] at h
      rw [Val.seq_sound x y h.1.1, Val.seq_sound x' y' h.1.2, Val.seqP_sound xs ys h.2]
theorem Val.seqE_sound : ∀ a b : List (String × Val), Val.seqE a b = true → a = b
  | [], b, h => by cases b <;> simp_all [Val.seqE]
  | (_, _) :: _, [], h => by simp [Val.seqE] at h
  | (x, x') :: xs, (y, y') :: ys, h => by
      simp [Val.seqE] at h
      rw [h.1.1, Val.seq_sound x' y' h.1.2, Val.seqE_sound xs ys h.2]
end

mutual
theorem Val.seq_refl : ∀ a : Val, Val.seq a a = true
  | .int _ | .str _ | .bool _ | .float _ | .unit | .ref _ | .iref _ _ | .fn _ => by
      simp [Val.seq]
  | .list xs => by simp [Val.seq, Val.seqL_refl xs]
  | .tuple xs => by simp [Val.seq, Val.seqL_refl xs]
  | .dict xs => by simp [Val.seq, Val.seqP_refl xs]
  | .clsClos _ xs => by simp [Val.seq, Val.seqE_refl xs]
  | .clos _ xs => by simp [Val.seq, Val.seqE_refl xs]
  | .bobj _ v => by simp [Val.seq, Val.seq_refl v]
theorem Val.seqL_refl : ∀ a : List Val, Val.seqL a a = true
  | [] => by simp [Val.seqL]
  | x :: xs => by simp [Val.seqL, Val.seq_refl x, Val.seqL_refl xs]
theorem Val.seqP_refl : ∀ a : List (Val × Val), Val.seqP a a = true
  | [] => by simp [Val.seqP]
  | (x, x') :: xs => by simp [Val.seqP, Val.seq_refl x, Val.seq_refl x', Val.seqP_refl xs]
theorem Val.seqE_refl : ∀ a : List (String × Val), Val.seqE a a = true
  | [] => by simp [Val.seqE]
  | (_, x') :: xs => by simp [Val.seqE, Val.seq_refl x', Val.seqE_refl xs]
end

instance : DecidableEq Val := fun a b =>
  decidable_of_iff (Val.seq a b = true) ⟨Val.seq_sound a b, fun h => h ▸ Val.seq_refl a⟩

deriving instance DecidableEq for Payload
deriving instance DecidableEq for Obj
deriving instance DecidableEq for EResult

-- The instances decide in the kernel, on nested values.
example : (Val.list [.int 1, .dict [(.str "k", .tuple [.unit])]]) =
    (Val.list [.int 1, .dict [(.str "k", .tuple [.unit])]]) := by decide +kernel
example : (Val.list [.int 1]) ≠ (Val.list [.int 2]) := by decide +kernel
example : (EResult.val (.clos "f" [("x", .bool true)])) ≠ EResult.hole "f" := by decide +kernel
example : ([{ cls := "<globals>", fields := [("x", .int 3)] }] : Heap) =
    [{ cls := "<globals>", fields := [("x", .int 3)] }] := by decide +kernel

end Autoform.Core
