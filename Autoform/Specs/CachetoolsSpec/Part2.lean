import Autoform.Refine
import Autoform.Generated.Cachetools
import Autoform.Specs.CachetoolsSpec.Base

/-! Part 2 of 6 of `Autoform/Specs/CachetoolsSpec.lean`: theorems only, moved verbatim;
the context is `CachetoolsSpec/Base.lean`. -/

namespace Autoform.Specs.Cachetools

open Autoform.Core Autoform.Refine Autoform.Generated.Cachetools

-- `local` attributes do not cross files; the same simp set as the single-file module.
attribute [local simp] Ctx.classLookupGap Ctx.usesClassMetadata Ctx.isProperty
  Ctx.classStorageKey Ctx.fieldWriteCheck Ctx.fieldWriteKey Ctx.readSlot Ctx.isSharedClassValue

/-! ### `Cache.maxsize` / `Cache.currsize` — the two accessors must read *different* fields

Stated for an arbitrary heap and an arbitrary receiver reference, so the field name is
not free to move: swapping `_Cache__maxsize` for `_Cache__currsize` makes the statement
false at any heap where the two differ. `Cache_size_fields_distinct` exhibits such a
heap explicitly, so the separation is witnessed and not merely implied. -/

/-- **The surplus-argument branch is part of the specification, not excluded from it.**
The rendered accessor has `params := []` — the receiver arrives as the base environment,
not as a positional parameter — so *any* positional argument is a surplus, and since
`posRejected` was made real the call raises `TypeError`, exactly as CPython does
(`maxsize() takes 1 positional argument but 2 were given`). The specification therefore
covers every argument list; before the calling convention was modelled the surplus was
silently truncated and this theorem's `.ret` branch was claimed for calls CPython
rejects. -/
-- RELAND: survived -- predicted to break (`@property` getter holed); property definitions translate now.
-- RELAND (2026-10-09): restated -- the receiver is a `Cache` (`HasClassField`).
theorem Cache_maxsize_mrefines :
    MRefines "cachetools/__init__.py:<module>.Cache.maxsize" 10
      (fun h self _ => ∃ r v, self = .ref r ∧ HasClassField h r "cachetools/__init__.py:<module>.Cache" "_Cache__maxsize" v)
      (fun h self args => (h, match args with
                           | [] => match self with
                                   | .ref r => .ret (readField h r "_Cache__maxsize")
                                   | _      => .ret .unit
                           | _  => .raise (.str "TypeError"))) := by
  rintro h _ args ⟨r, v, rfl, o, hg, hcls, hfld⟩
  refine forall_ge_of_forall_add (N := 10) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__Cache_maxsize rfl]
  cases args with
  | nil =>
    simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set, f_cachetools___init___py__module__Cache_maxsize, ctxOf, P, P_dialect, readField, hg, hcls, hfld, lookup_Cache_maxsize]
  | cons a as =>
    simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Outcome.toEResult, f_cachetools___init___py__module__Cache_maxsize]

/-- **The surplus-argument branch is part of the specification, not excluded from it.**
The rendered accessor has `params := []` — the receiver arrives as the base environment,
not as a positional parameter — so *any* positional argument is a surplus, and since
`posRejected` was made real the call raises `TypeError`, exactly as CPython does
(`maxsize() takes 1 positional argument but 2 were given`). The specification therefore
covers every argument list; before the calling convention was modelled the surplus was
silently truncated and this theorem's `.ret` branch was claimed for calls CPython
rejects. -/
-- RELAND: survived -- predicted to break (`@property` getter holed); property definitions translate now.
-- RELAND (2026-10-09): restated -- the receiver is a `Cache` (`HasClassField`).
theorem Cache_currsize_mrefines :
    MRefines "cachetools/__init__.py:<module>.Cache.currsize" 10
      (fun h self _ => ∃ r v, self = .ref r ∧ HasClassField h r "cachetools/__init__.py:<module>.Cache" "_Cache__currsize" v)
      (fun h self args => (h, match args with
                           | [] => match self with
                                   | .ref r => .ret (readField h r "_Cache__currsize")
                                   | _      => .ret .unit
                           | _  => .raise (.str "TypeError"))) := by
  rintro h _ args ⟨r, v, rfl, o, hg, hcls, hfld⟩
  refine forall_ge_of_forall_add (N := 10) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__Cache_currsize rfl]
  cases args with
  | nil =>
    simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set, f_cachetools___init___py__module__Cache_currsize, ctxOf, P, P_dialect, readField, hg, hcls, hfld, lookup_Cache_currsize]
  | cons a as =>
    simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Outcome.toEResult, f_cachetools___init___py__module__Cache_currsize]

/-- A concrete cache object whose capacity and occupancy differ. -/
def sampleCache : Heap :=
  [{ cls := "cachetools/__init__.py:<module>.Cache"
   , fields := [("_Cache__maxsize", .int 128), ("_Cache__currsize", .int 3)] }]

/-- The two accessors read the two fields, and are therefore observably different
functions on a cache whose capacity and occupancy differ.

**This statement was strengthened because the mutation gate said so.** It first read only
`maxsize ≠ currsize`, and scored **0/8** — every single-function mutant preserves a
*difference* (breaking one accessor leaves the other alone, so the two still disagree),
so an inequality between two functions is not evidence about either of them. Pinning both
values is what gives it teeth. The lesson generalises: a witness that asserts a relation
between two computations tests neither unless the relation is pinned on both sides. -/
-- RELAND: survived -- predicted to break (both getters holed); property definitions translate now.
theorem Cache_size_fields_distinct :
    (runMethod 10 sampleCache "cachetools/__init__.py:<module>.Cache.maxsize" (.ref 0) []).2
        = .val (.int 128)
  ∧ (runMethod 10 sampleCache "cachetools/__init__.py:<module>.Cache.currsize" (.ref 0) []).2
        = .val (.int 3)
  ∧ (runMethod 10 sampleCache "cachetools/__init__.py:<module>.Cache.maxsize" (.ref 0) []).2
      ≠ (runMethod 10 sampleCache "cachetools/__init__.py:<module>.Cache.currsize" (.ref 0) []).2 := by
  -- Evaluated by the kernel on the concrete heap, not derived from the parent theorems:
  -- a witness that re-derives from an unchanged statement is invisible to the mutation
  -- gate (§4, finding 1), and this one scored 0/4 that way on 2026-10-09.
  refine ⟨rfl, rfl, ?_⟩
  show EResult.val (.int 128) ≠ EResult.val (.int 3)
  intro he; cases he

end Autoform.Specs.Cachetools
