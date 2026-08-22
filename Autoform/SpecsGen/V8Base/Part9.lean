import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part9

def ob_returns_v8_base_OS_Initialize_duplicate_0_void_char : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_returns_v8_base_OS_Initialize_duplicate_0_void_char).all (lawReturns C fuel f_v8_base_OS_Initialize_duplicate_0_void_char__)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_idempotent_v8_base_OS_Initialize_duplicate_0_void_char rather than proved; see the module header for the measured cost.
theorem idempotent_v8_base_OS_Initialize_duplicate_0_void_char_at_FUEL : ((dom_idempotent_v8_base_OS_Initialize_duplicate_0_void_char).all (lawIdempotent C FUEL f_v8_base_OS_Initialize_duplicate_0_void_char__)) = true := by rfl

def ob_idempotent_v8_base_OS_Initialize_duplicate_0_void_char : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_idempotent_v8_base_OS_Initialize_duplicate_0_void_char).all (lawIdempotent C fuel f_v8_base_OS_Initialize_duplicate_0_void_char__)) = true


theorem uconst_v8_base_OS_IsHardwareEnforcedShadowStacksEnabled_bool :
    Refines P "v8.base.OS.IsHardwareEnforcedShadowStacksEnabled:bool()" 8
      (fun args => posRejected f_v8_base_OS_IsHardwareEnforcedShadowStacksEnabled_bool__ args = false)
      (fun _ => .ret (Val.bool false)) := by
  intro args hdom
  simp [posRejected, f_v8_base_OS_IsHardwareEnforcedShadowStacksEnabled_bool__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_OS_IsHardwareEnforcedShadowStacksEnabled_bool__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_IsHardwareEnforcedShadowStacksEnabled_bool__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_IsHardwareEnforcedShadowStacksEnabled_bool__, ctxOf, P, hdom]


end Autoform.SpecsGen.V8Base.Part9
