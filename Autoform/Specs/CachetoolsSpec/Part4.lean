import Autoform.Refine
import Autoform.Generated.Cachetools
import Autoform.Specs.CachetoolsSpec.Base

/-! Part 4 of 6 of `Autoform/Specs/CachetoolsSpec.lean`: theorems only, moved verbatim;
the context is `CachetoolsSpec/Base.lean`. -/

namespace Autoform.Specs.Cachetools

open Autoform.Core Autoform.Refine Autoform.Generated.Cachetools

-- `local` attributes do not cross files; the same simp set as the single-file module.
attribute [local simp] Ctx.classLookupGap Ctx.usesClassMetadata Ctx.isProperty
  Ctx.classStorageKey Ctx.fieldWriteCheck Ctx.fieldWriteKey Ctx.readSlot Ctx.isSharedClassValue

/-! ### `_TimedCache._Timer.__init__` — both assignments happen

A constructor is specified by the *whole* post-state. Deleting either branch of the
`Stmt.seq` changes the resulting heap, so the mutation gate's `seq`-deletion operator has
something to break here. -/

-- RELAND: survives. RELAND (2026-10-09): restated -- the receiver is a `_Timer` (`HasClass`).
theorem Timer_init_mrefines :
    MRefines "cachetools/__init__.py:<module>._TimedCache._Timer.__init__" 12
      (fun h self args => ∃ r t, self = .ref r ∧ args = [t] ∧ HasClass h r "cachetools/__init__.py:<module>._TimedCache._Timer")
      (fun h self args => match self, args with
                          | .ref r, [t] =>
                              (((h.setField r "_Timer__timer" t).setField r "_Timer__nesting" (.int 0)),
                               .ret .unit)
                          | _, _ => (h, .ret .unit)) := by
  rintro h _ _ ⟨r, t, rfl, rfl, o, hg, hcls⟩
  refine forall_ge_of_forall_add (N := 12) ?_
  intro m
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module___TimedCache__Timer___init__ rfl]
  simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___TimedCache__Timer___init__, ctxOf, P, P_dialect,
        Heap.get_setField, hg, hcls, lookup_Timer_timer, lookup_Timer_nesting, lookup_Timer_setattr, allowsDict_Timer]

end Autoform.Specs.Cachetools
