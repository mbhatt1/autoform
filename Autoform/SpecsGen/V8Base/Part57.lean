import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part57

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_involutive_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot rather than proved; see the module header for the measured cost.
theorem involutive_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_at_FUEL : ((dom_involutive_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot).all (lawInvolutive C FUEL f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_)) = true := by rfl

def ob_involutive_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_involutive_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot).all (lawInvolutive C fuel f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_)) = true


theorem uproj_v8_base_Semaphore_native_handle_NativeHandle :
    MRefines P "v8.base.Semaphore.native_handle:NativeHandle()" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "native_handle_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Semaphore_native_handle_NativeHandle__ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Semaphore_native_handle_NativeHandle__ "native_handle_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_Semaphore_native_handle_ANY___const :
    MRefines P "v8.base.Semaphore.native_handle:ANY()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "native_handle_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Semaphore_native_handle_ANY___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Semaphore_native_handle_ANY___const_ "native_handle_" rfl rfl rfl rfl r [] rfl
      hmod


end Autoform.SpecsGen.V8Base.Part57
