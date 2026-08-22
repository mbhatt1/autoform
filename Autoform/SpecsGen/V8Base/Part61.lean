import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part61

theorem uconst_v8_base_VirtualAddressSubspace_CanAllocateSubspaces_bool :
    Refines P "v8.base.VirtualAddressSubspace.CanAllocateSubspaces:bool()" 8
      (fun args => posRejected f_v8_base_VirtualAddressSubspace_CanAllocateSubspaces_bool__ args = false)
      (fun _ => .ret (Val.bool true)) := by
  intro args hdom
  simp [posRejected, f_v8_base_VirtualAddressSubspace_CanAllocateSubspaces_bool__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_VirtualAddressSubspace_CanAllocateSubspaces_bool__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_VirtualAddressSubspace_CanAllocateSubspaces_bool__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_VirtualAddressSubspace_CanAllocateSubspaces_bool__, ctxOf, P, hdom]

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_charact_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t rather than proved; see the module header for the measured cost.
theorem charact_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t_at_FUEL : ((dom_charact_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t).all (lawConform C FUEL f_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t_)) = true := by rfl

def ob_charact_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_charact_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t).all (lawConform C fuel f_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t_)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_charact_v8_base_bits_SignedMod64_int64_t_int64_t_int64_t rather than proved; see the module header for the measured cost.

end Autoform.SpecsGen.V8Base.Part61
