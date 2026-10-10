import Autoform.Refine
import Autoform.Generated.Cachetools
import Autoform.Specs.CachetoolsSpec.Base

/-! Part 3 of 6 of `Autoform/Specs/CachetoolsSpec.lean`: theorems only, moved verbatim;
the context is `CachetoolsSpec/Base.lean`. -/

namespace Autoform.Specs.Cachetools

open Autoform.Core Autoform.Refine Autoform.Generated.Cachetools

-- `local` attributes do not cross files; the same simp set as the single-file module.
attribute [local simp] Ctx.classLookupGap Ctx.usesClassMetadata Ctx.isProperty
  Ctx.classStorageKey Ctx.fieldWriteCheck Ctx.fieldWriteKey Ctx.readSlot Ctx.isSharedClassValue

/-! ### `Cache.__contains__` — membership, and the *polarity* of `in`

`Expr.inOp` carries a negation flag. `__contains__` must use the positive one; a flipped
flag is a silent inversion of every containment test in the library, which this theorem
refutes on any dict receiver. -/

-- RELAND: survives. RELAND (2026-10-09): restated -- the receiver is a `Cache`.
theorem Cache_contains_mrefines :
    MRefines "cachetools/__init__.py:<module>.Cache.__contains__" 12
      (fun h self args => ∃ r k kvs, self = .ref r ∧ args = [k]
                            ∧ HasClassField h r "cachetools/__init__.py:<module>.Cache" "_Cache__data" (.dict kvs))
      (fun h self args => (h, match self, args with
                              | .ref r, [k] =>
                                  match readField h r "_Cache__data" with
                                  | .dict kvs => .ret (.bool (kvs.any (fun kv => Val.beq k kv.1)))
                                  | _         => .ret .unit
                              | _, _ => .ret .unit)) := by
  rintro h _ _ ⟨r, k, kvs, rfl, rfl, o, hg, hcls, hfld⟩
  refine forall_ge_of_forall_add (N := 12) ?_
  intro n
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__Cache___contains__ rfl]
  simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module__Cache___contains__, ctxOf, P, P_dialect, valIn, readField,
        Ctx.dunderOn, Val.unbox, hg, hcls, hfld, lookup_Cache_data]

/-- Membership is not constant: it answers `true` for a present key and `false` for an
absent one. This is the anti-vacuity witness for `Cache_contains_mrefines` — a
specification satisfied by `fun _ => true` would pass the equation above only if that
equation were itself wrong, and this makes the discrimination concrete. -/
-- RELAND: survives.
theorem Cache_contains_discriminates :
    (runMethod 12 [{ cls := "cachetools/__init__.py:<module>.Cache", fields := [("_Cache__data", .dict [(.int 1, .int 9)])] }]
        "cachetools/__init__.py:<module>.Cache.__contains__" (.ref 0) [.int 1]).2 = .val (.bool true)
  ∧ (runMethod 12 [{ cls := "cachetools/__init__.py:<module>.Cache", fields := [("_Cache__data", .dict [(.int 1, .int 9)])] }]
        "cachetools/__init__.py:<module>.Cache.__contains__" (.ref 0) [.int 2]).2 = .val (.bool false) := by
  exact ⟨rfl, rfl⟩

/-! ### `TLRUCache._Item.__lt__` — retired

RELAND (2026-10-09): `TLRUItem_lt_mrefines` and `TLRUItem_lt_irrefl` are deleted. `_Item`
is decorated with `functools.total_ordering`, a decorator the exporter cannot apply, so
the re-landed program records the class as `class-definition:decorator-or-metaclass`: no
attribute of an `_Item` instance is readable through its namespace, and a theorem about
`__lt__` reading `self.expires` would be a theorem about that hole. The strict-order claim
is still the right specification; what it needs is a contract for `total_ordering` (it
adds the three missing comparison methods and touches nothing else), the same mechanism
as the external base-class contracts, and that is future work rather than a restated
weaker theorem. -/

/-! ### `_TimedCache._Timer.__exit__` — a heap effect, specified exactly

The timer's re-entrancy counter is decremented on exit. This is the only place in these
specifications where the *heap* is the observable, and it is stated as an exact equation
on `Heap.setField`, so `-` → `+` and `1` → `2` are both refuted. -/

-- RELAND: survives. RELAND (2026-10-09): restated -- the receiver is a `_Timer`. `_Timer`
-- defines `__getattr__`; the exporter used to make that a barrier on the whole namespace,
-- now it is a miss-only hook (docs/languages.md §16.A), and `_Timer__nesting` is present.
theorem Timer_exit_mrefines :
    MRefines "cachetools/__init__.py:<module>._TimedCache._Timer.__exit__" 12
      (fun h self args => ∃ r n e, self = .ref r ∧ args = [e]
                            ∧ HasClassField h r "cachetools/__init__.py:<module>._TimedCache._Timer" "_Timer__nesting" (.int n))
      (fun h self _ => match self with
                       | .ref r =>
                           match readField h r "_Timer__nesting" with
                           | .int n => (h.setField r "_Timer__nesting" (.int (n - 1)), .ret .unit)
                           | _      => (h, .ret .unit)
                       | _ => (h, .ret .unit)) := by
  rintro h _ _ ⟨r, n, e, rfl, rfl, o, hg, hcls, hfld⟩
  refine forall_ge_of_forall_add (N := 12) ?_
  intro m
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module___TimedCache__Timer___exit__ rfl]
  simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___TimedCache__Timer___exit__, ctxOf, P,
        P_dialect, readField, hg, hcls, hfld, lookup_Timer_nesting, lookup_Timer_setattr, allowsDict_Timer]

/-- The decrement is a decrement: on a concrete timer at nesting 1, exit leaves 0. -/
-- RELAND: survives.
theorem Timer_exit_decrements :
    readField ((runMethod 12 [{ cls := "cachetools/__init__.py:<module>._TimedCache._Timer", fields := [("_Timer__nesting", .int 1)] }]
        "cachetools/__init__.py:<module>._TimedCache._Timer.__exit__" (.ref 0) [.unit]).1) 0
        "_Timer__nesting" = .int 0 := by
  rfl

end Autoform.Specs.Cachetools
