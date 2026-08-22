import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part5

theorem idempotent_v8_base_SetFatalFunction_void_void_at_FUEL : ((dom_idempotent_v8_base_SetFatalFunction_void_void).all (lawIdempotent C FUEL f_v8_base_SetFatalFunction_void_void_)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem idempotent_v8_base_SetFatalFunction_void_void : ∀ fuel, FUEL ≤ fuel → ((dom_idempotent_v8_base_SetFatalFunction_void_void).all (lawIdempotent C fuel f_v8_base_SetFatalFunction_void_void_)) = true := by
  intro fuel hf
  exact all_transfer _ (gIdem C FUEL f_v8_base_SetFatalFunction_void_void_) (lawIdempotent C FUEL f_v8_base_SetFatalFunction_void_void_) (lawIdempotent C fuel f_v8_base_SetFatalFunction_void_void_)
    (fun c hgc hlc =>
      lawIdempotent_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_SetFatalFunction_void_void_.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)


def ob_idempotent_v8_base_SetFatalFunction_void_void : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_idempotent_v8_base_SetFatalFunction_void_void).all (lawIdempotent C fuel f_v8_base_SetFatalFunction_void_void_)) = true


theorem uproj_v8_base_SharedMemoryMapping_GetMemory_void____const :
    MRefines P "v8.base.SharedMemoryMapping.GetMemory:void*()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "ptr_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_SharedMemoryMapping_GetMemory_void____const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_SharedMemoryMapping_GetMemory_void____const_ "ptr_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_SharedMemory_GetMemory_void____const :
    MRefines P "v8.base.SharedMemory.GetMemory:void*()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "ptr_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_SharedMemory_GetMemory_void____const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_SharedMemory_GetMemory_void____const_ "ptr_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_SharedMemory_GetSize_size_t___const :
    MRefines P "v8.base.SharedMemory.GetSize:size_t()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "size_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_SharedMemory_GetSize_size_t___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_SharedMemory_GetSize_size_t___const_ "size_" rfl rfl rfl rfl r [] rfl
      hmod


end Autoform.SpecsGen.V8Base.Part5
