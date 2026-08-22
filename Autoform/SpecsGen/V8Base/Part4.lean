import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part4

theorem uconst_v8_base_FPU_GetFlushDenormals_bool :
    Refines P "v8.base.FPU.GetFlushDenormals:bool()" 8
      (fun args => posRejected f_v8_base_FPU_GetFlushDenormals_bool__ args = false)
      (fun _ => .ret (Val.bool false)) := by
  intro args hdom
  simp [posRejected, f_v8_base_FPU_GetFlushDenormals_bool__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_FPU_GetFlushDenormals_bool__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_FPU_GetFlushDenormals_bool__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_FPU_GetFlushDenormals_bool__, ctxOf, P, hdom]

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_idempotent_v8_base_SetPrintStackTrace_void_void rather than proved; see the module header for the measured cost.
theorem idempotent_v8_base_SetPrintStackTrace_void_void_at_FUEL : ((dom_idempotent_v8_base_SetPrintStackTrace_void_void).all (lawIdempotent C FUEL f_v8_base_SetPrintStackTrace_void_void_)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem idempotent_v8_base_SetPrintStackTrace_void_void : ∀ fuel, FUEL ≤ fuel → ((dom_idempotent_v8_base_SetPrintStackTrace_void_void).all (lawIdempotent C fuel f_v8_base_SetPrintStackTrace_void_void_)) = true := by
  intro fuel hf
  exact all_transfer _ (gIdem C FUEL f_v8_base_SetPrintStackTrace_void_void_) (lawIdempotent C FUEL f_v8_base_SetPrintStackTrace_void_void_) (lawIdempotent C fuel f_v8_base_SetPrintStackTrace_void_void_)
    (fun c hgc hlc =>
      lawIdempotent_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_SetPrintStackTrace_void_void_.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)


def ob_idempotent_v8_base_SetPrintStackTrace_void_void : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_idempotent_v8_base_SetPrintStackTrace_void_void).all (lawIdempotent C fuel f_v8_base_SetPrintStackTrace_void_void_)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_idempotent_v8_base_SetFatalFunction_void_void rather than proved; see the module header for the measured cost.

end Autoform.SpecsGen.V8Base.Part4
