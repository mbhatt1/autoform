import Autoform.Refine
import Autoform.Generated.Cachetools
import Autoform.Specs.CachetoolsSpec.Base

/-! Part 1 of 6 of `Autoform/Specs/CachetoolsSpec.lean`: theorems only, moved verbatim;
the context is `CachetoolsSpec/Base.lean`. -/

namespace Autoform.Specs.Cachetools

open Autoform.Core Autoform.Refine Autoform.Generated.Cachetools

-- `local` attributes do not cross files; the same simp set as the single-file module.
attribute [local simp] Ctx.classLookupGap Ctx.usesClassMetadata Ctx.isProperty
  Ctx.classStorageKey Ctx.fieldWriteCheck Ctx.fieldWriteKey Ctx.readSlot Ctx.isSharedClassValue

/-! ### `Cache.getsizeof` — the size model is the constant 1

`cachetools.Cache.getsizeof` is the default cost function: every entry costs 1. This is
the assumption the whole `currsize`/`maxsize` accounting rests on, so it is worth
pinning rather than assuming. -/

/-! **Re-land assessment (cachetools v7.1.7 under the current exporter).**

Every subject below was looked up in a fresh export of the identified revision, and each
theorem is annotated with what happens to it when `ast-Cachetools.json` is replaced:

* `RELAND: survives` -- the function is hole-free and its body is byte-identical to the
  committed one; only the added `signatureRejected`/`Func.keywordParams` simp arguments
  are needed, because the fresh render carries a real `pythonSignature` and
  `signatureRejected_legacy` no longer discharges the check.
* `RELAND: BREAKS -- getter is a hole` -- was the prediction for `Cache.maxsize` and
  `Cache.currsize`, `@property` getters the exporter used to hole as
  `call:python-receiver-signature`. Property definitions translate now
  (`Program.properties`, docs/languages.md §12/§14), so on the re-land these theorems
  SURVIVED unchanged; the annotation is kept as the record of what was expected.
* `RELAND: replaced` -- the two `cache_clear` theorems asserted that the function REACHES
  `scope:nonlocal-write`. It no longer does: `nonlocal` writes are boxed
  (docs/languages.md §11), the function is hole-free, and the negative result was false
  in the good direction. §3 now states what the function does instead.
* `RELAND: verified` -- hole-free but the body differed from the committed one; checked
  on the first build against the re-landed AST (`ast-Cachetools.json`, cachetools v7.1.7,
  Joern 4.0.606 -- see `provenance/ast-Cachetools.json.prov.json`).
-/
-- RELAND: survives (staticmethod fix restored `return 1`; body byte-identical).
theorem Cache_getsizeof_refines :
    Refines₁ (α := Int) (β := Int) P
      "cachetools/__init__.py:<module>.Cache.getsizeof" 8 (fun _ => True) (fun _ => 1) := by
  intro v _
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_cachetools___init___py__module__Cache_getsizeof rfl]
  simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module__Cache_getsizeof, ctxOf, P, Marshal.toVal]

/-! ### `_DefaultSize.__getitem__` / `.pop` — the degenerate size table

`_DefaultSize` is the object `Cache` uses when no `getsizeof` was supplied: a mapping
that answers `1` to every lookup and forgets every write. Both halves are specified. -/

-- RELAND: survives.
theorem DefaultSize_getitem_refines :
    Refines₁ (α := Int) (β := Int) P
      "cachetools/__init__.py:<module>._DefaultSize.__getitem__" 8
      (fun _ => True) (fun _ => 1) := by
  intro v _
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_cachetools___init___py__module___DefaultSize___getitem__ rfl]
  simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___DefaultSize___getitem__, ctxOf, P, Marshal.toVal]

-- RELAND: survives.
theorem DefaultSize_pop_refines :
    Refines₁ (α := Int) (β := Int) P
      "cachetools/__init__.py:<module>._DefaultSize.pop" 8
      (fun _ => True) (fun _ => 1) := by
  intro v _
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_cachetools___init___py__module___DefaultSize_pop rfl]
  simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___DefaultSize_pop, ctxOf, P, Marshal.toVal]

/-- `_DefaultSize.__setitem__` is a no-op **on the heap as well as on the result**: this
is the theorem that would catch the store being silently implemented. -/
-- RELAND: survives.
theorem DefaultSize_setitem_mrefines :
    MRefines "cachetools/__init__.py:<module>._DefaultSize.__setitem__" 8
      (fun _ _ args => ∃ k v, args = [k, v])
      (fun h _ _ => (h, .ret .unit)) := by
  rintro h self _ ⟨a, b, rfl⟩
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module___DefaultSize___setitem__ rfl]
  simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___DefaultSize___setitem__, ctxOf, P]

end Autoform.Specs.Cachetools
