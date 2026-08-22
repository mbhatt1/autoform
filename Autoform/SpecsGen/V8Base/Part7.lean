import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part7

theorem uconst_v8_base_OS_CanReserveAddressSpace_bool :
    Refines P "v8.base.OS.CanReserveAddressSpace:bool()" 8
      (fun args => posRejected f_v8_base_OS_CanReserveAddressSpace_bool__ args = false)
      (fun _ => .ret (Val.bool true)) := by
  intro args hdom
  simp [posRejected, f_v8_base_OS_CanReserveAddressSpace_bool__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_OS_CanReserveAddressSpace_bool__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_CanReserveAddressSpace_bool__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_CanReserveAddressSpace_bool__, ctxOf, P, hdom]

theorem uconst_v8_base_OS_HasLazyCommits_duplicate_0_bool :
    Refines P "v8.base.OS.HasLazyCommits<duplicate>0:bool()" 8
      (fun args => posRejected f_v8_base_OS_HasLazyCommits_duplicate_0_bool__ args = false)
      (fun _ => .ret (Val.bool true)) := by
  intro args hdom
  simp [posRejected, f_v8_base_OS_HasLazyCommits_duplicate_0_bool__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_OS_HasLazyCommits_duplicate_0_bool__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_HasLazyCommits_duplicate_0_bool__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_HasLazyCommits_duplicate_0_bool__, ctxOf, P, hdom]

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_idempotent_v8_base_PosixInitializeCommon_void_char rather than proved; see the module header for the measured cost.
theorem idempotent_v8_base_PosixInitializeCommon_void_char_at_FUEL : ((dom_idempotent_v8_base_PosixInitializeCommon_void_char).all (lawIdempotent C FUEL f_v8_base_PosixInitializeCommon_void_char__)) = true := by rfl

def ob_idempotent_v8_base_PosixInitializeCommon_void_char : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_idempotent_v8_base_PosixInitializeCommon_void_char).all (lawIdempotent C fuel f_v8_base_PosixInitializeCommon_void_char__)) = true



end Autoform.SpecsGen.V8Base.Part7
