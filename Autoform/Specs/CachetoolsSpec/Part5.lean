import Autoform.Refine
import Autoform.Generated.Cachetools
import Autoform.Specs.CachetoolsSpec.Base

/-! Part 5 of 6 of `Autoform/Specs/CachetoolsSpec.lean`: theorems only, moved verbatim;
the context is `CachetoolsSpec/Base.lean`. -/

namespace Autoform.Specs.Cachetools

open Autoform.Core Autoform.Refine Autoform.Generated.Cachetools

-- `local` attributes do not cross files; the same simp set as the single-file module.
attribute [local simp] Ctx.classLookupGap Ctx.usesClassMetadata Ctx.isProperty
  Ctx.classStorageKey Ctx.fieldWriteCheck Ctx.fieldWriteKey Ctx.readSlot Ctx.isSharedClassValue

/-- Both fields are actually written, with the right values in the right places. -/
-- RELAND: survives.
theorem Timer_init_sets_both :
    readField (runMethod 12 [{ cls := "cachetools/__init__.py:<module>._TimedCache._Timer", fields := [] }]
        "cachetools/__init__.py:<module>._TimedCache._Timer.__init__" (.ref 0) [.int 99]).1
      0 "_Timer__timer" = .int 99
  ∧ readField (runMethod 12 [{ cls := "cachetools/__init__.py:<module>._TimedCache._Timer", fields := [] }]
        "cachetools/__init__.py:<module>._TimedCache._Timer.__init__" (.ref 0) [.int 99]).1
      0 "_Timer__nesting" = .int 0 := by
  exact ⟨rfl, rfl⟩

/-! ### `TTLCache.__setstate__.<lambda>0` — a projection out of an *argument*, not `self` -/

-- RELAND: survives. RELAND (2026-10-09): restated -- the argument is a `_Link`, whose
-- `expires` is a slot read from its storage key.
theorem TTLSetstate_lambda_mrefines :
    MRefines "cachetools/__init__.py:<module>.TTLCache.__setstate__.<lambda>0" 10
      (fun h _ args => ∃ r v, args = [.ref r] ∧ HasClassField h r "cachetools/__init__.py:<module>.TTLCache._Link" "<slot>cachetools/__init__.py:<module>.TTLCache._Link.expires" v)
      (fun h _ args => (h, match args with
                           | [.ref r] => .ret (readField h r "<slot>cachetools/__init__.py:<module>.TTLCache._Link.expires")
                           | _        => .ret .unit)) := by
  rintro h self _ ⟨r, v, rfl, o, hg, hcls, hfld⟩
  refine forall_ge_of_forall_add (N := 10) ?_
  intro m
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__TTLCache___setstate____lambda_0 rfl]
  simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module__TTLCache___setstate____lambda_0, ctxOf, P, P_dialect,
        readField, hg, hcls, hfld, lookup_Link_expires]

/-! ### `_TimedCache.expire` — an *exception* is a specification

`_TimedCache.expire` is Python's abstract-method idiom: it raises. `Outcome.raise` is a
legitimate refinement target (see `Refine.lean` §1), so "this method always raises" is a
complete specification rather than a gap, and `.raise` → `.ret` is refuted by it.

The re-landed export spells `raise NotImplementedError` as the
`py:exception:NotImplementedError` constructor, whose value IS the class name, and
`Stmt.raise` under `.python` classifies what it raises (`pythonRaise`): a represented
class name passes through unchanged. So the statement names the class — the caveat that
stood here ("raises, but the payload is `unit`") is closed, and obligation (3) in §4
records what is still not modelled: the exception's *arguments*. -/

-- RELAND: verified on the re-landed body (`raise` of the `py:exception:` constructor).
theorem TimedCache_expire_raises (t : Val) (fuel : Nat) (hf : 10 ≤ fuel) :
    runFunc P fuel "cachetools/__init__.py:<module>._TimedCache.expire" [t]
      = .exn (.str "NotImplementedError") := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 10 := ⟨fuel - 10, by omega⟩
  rw [runFunc_of_resolve _ _ _ _ f_cachetools___init___py__module___TimedCache_expire rfl]
  have hne : ((none : Option String) != some "time") = true := rfl
  simp +decide only [hne, applyFunc, seedClassAttrDefaults, seedClassAttrs, Func.classAttrDefaults, selfEnv,
        bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams,
        Option.map, Option.getD, List.length, Bool.and_false, Bool.true_and, Bool.or_false, Bool.false_or,
        Val.unbuiltin, execStmt, f_cachetools___init___py__module___TimedCache_expire,
        Env.set, List.filter, List.any, Option.isNone, bne_iff_ne, ne_eq,
        reduceCtorEq, not_false_eq_true, decide_true, Bool.and_self]
  -- The constructor's name is a `String.drop` the kernel computes; `startsWith` is a
  -- simproc. Establish the name first so the rewrite has a literal to work with.
  have hname : ("py:exception:NotImplementedError".drop "py:exception:".length).toString
      = "NotImplementedError" := by decide
  have hname' : ("py:exception:NotImplementedError".drop "py:exception:".length).copy
      = "NotImplementedError" := by decide
  simp +decide [evalExpr, evalList, applyUnop, hname, hname', Stdlib.makeException,
                Stdlib.excNames, pythonRaise, ctxOf, P]

/-! ### `_cachedmethod._none` — the sentinel is constant -/

-- RELAND: survives.
theorem cachedmethod_none_refines :
    Refines P "cachetools/_cachedmethod.py:<module>._none" 8
      (fun args => ∃ x, args = [x]) (fun _ => .ret .unit) := by
  rintro _ ⟨x, rfl⟩
  refine forall_ge_of_forall_add (N := 8) ?_
  intro m
  rw [runFunc_of_resolve _ _ _ _ f_cachetools__cachedmethod_py__module___none rfl]
  simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools__cachedmethod_py__module___none, ctxOf, P]

/-! ## 3. The former negative result, now a positive one

`Refine.lean` proves `sample_id_not_refinable` on a copied term, and this section used to
prove the same thing about the REAL module: `_uncached_info.cache_clear` writes a
closed-over variable, `nonlocal` writes were an honest hole (`scope:nonlocal-write`), and
no shallow specification could refine a hole. That negative result is now false in the
good direction. `nonlocal` is boxed: `_uncached_info` allocates `misses` as a heap cell
(`Expr.boxNew`) and the closure captures the reference, so `cache_clear` translates to
`misses.v = 0` on that cell. The theorem that replaces the negative one says exactly what
the function does when called with its captured box: it returns `None` and the box's `v`
is `0` afterwards — stated with `Heap.setField` on the left so nothing about the rest of
the heap is assumed or lost. -/

-- RELAND: replaced -- `nonlocal` is boxed, the function translates, and the negative result
-- it stood for (`cache_clear_reaches_hole`, `cache_clear_not_refinable`) is now false.
-- RELAND (2026-10-09): the box at `r` is named as what it is (`Expr.boxNew` allocates
-- class `<local>`): with class metadata a write consults the receiver's class, and a box
-- has none.
theorem cache_clear_zeroes_the_box (k : Nat) (h : Heap) (r : Ref) (hb : HasClass h r "<local>") :
    applyClosure (ctxOf P) (k + 5) h
        f_cachetools__cached_py__module___uncached_info_cache_clear [("misses", .ref r)] [] []
      = (h.setField r "v" (.int 0), .val .unit) := by
  obtain ⟨o, hg, hcls⟩ := hb
  simp +decide [applyClosure, seedClassAttrDefaults, seedClassAttrs, Func.classAttrDefaults,
        bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected,
        signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools__cached_py__module___uncached_info_cache_clear, hg, hcls]

end Autoform.Specs.Cachetools
