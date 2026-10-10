import Autoform.Refine
import Autoform.Generated.Cachetools
import Autoform.Specs.CachetoolsSpec.Base

/-! Part 6 of 6 of `Autoform/Specs/CachetoolsSpec.lean`: theorems only, moved verbatim;
the context is `CachetoolsSpec/Base.lean`. -/

namespace Autoform.Specs.Cachetools

open Autoform.Core Autoform.Refine Autoform.Generated.Cachetools

-- `local` attributes do not cross files; the same simp set as the single-file module.
attribute [local simp] Ctx.classLookupGap Ctx.usesClassMetadata Ctx.isProperty
  Ctx.classStorageKey Ctx.fieldWriteCheck Ctx.fieldWriteKey Ctx.readSlot Ctx.isSharedClassValue

/-! ### `TTLCache._Link.__init__` — the same shape, a different pair of fields

`_Link` declares `__slots__ = ("expires", "key", "next", "prev")`, so RELAND (2026-10-09)
its two writes land in the slots' storage keys (`<slot><class>.<name>`, the key the oracle
also snapshots), not in a dictionary entry named `key`. The specification says so. -/

-- RELAND: survives. RELAND (2026-10-09): restated -- slot storage keys, receiver a `_Link`.
theorem TTLLink_init_mrefines :
    MRefines "cachetools/__init__.py:<module>.TTLCache._Link.__init__" 12
      (fun h self args => ∃ r k e, self = .ref r ∧ args = [k, e] ∧ HasClass h r "cachetools/__init__.py:<module>.TTLCache._Link")
      (fun h self args => match self, args with
                          | .ref r, [k, e] =>
                              (((h.setField r "<slot>cachetools/__init__.py:<module>.TTLCache._Link.key" k).setField r "<slot>cachetools/__init__.py:<module>.TTLCache._Link.expires" e), .ret .unit)
                          | _, _ => (h, .ret .unit)) := by
  rintro h _ _ ⟨r, k, e, rfl, rfl, o, hg, hcls⟩
  refine forall_ge_of_forall_add (N := 12) ?_
  intro m
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__TTLCache__Link___init__ rfl]
  simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module__TTLCache__Link___init__, ctxOf, P, P_dialect,
        Heap.get_setField, hg, hcls, lookup_Link_setattr, lookup_Link_key, lookup_Link_expires]

end Autoform.Specs.Cachetools
