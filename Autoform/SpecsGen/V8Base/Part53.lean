import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part53

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_commutes_v8_base_MulWithWraparound_int16_t_int16_t_int16_t rather than proved; see the module header for the measured cost.
theorem commutes_v8_base_MulWithWraparound_int16_t_int16_t_int16_t_at_FUEL : ((dom_commutes_v8_base_MulWithWraparound_int16_t_int16_t_int16_t).all (lawCommutes C FUEL f_v8_base_MulWithWraparound_int16_t_int16_t_int16_t_)) = true := by rfl

def ob_commutes_v8_base_MulWithWraparound_int16_t_int16_t_int16_t : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_commutes_v8_base_MulWithWraparound_int16_t_int16_t_int16_t).all (lawCommutes C fuel f_v8_base_MulWithWraparound_int16_t_int16_t_int16_t_)) = true


theorem uproj_v8_base_PageAllocator_AllocatePageSize_size_t :
    MRefines P "v8.base.PageAllocator.AllocatePageSize:size_t()" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "allocate_page_size_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_PageAllocator_AllocatePageSize_size_t__ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_PageAllocator_AllocatePageSize_size_t__ "allocate_page_size_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_PageAllocator_CommitPageSize_size_t :
    MRefines P "v8.base.PageAllocator.CommitPageSize:size_t()" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "commit_page_size_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_PageAllocator_CommitPageSize_size_t__ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_PageAllocator_CommitPageSize_size_t__ "commit_page_size_" rfl rfl rfl rfl r [] rfl
      hmod


end Autoform.SpecsGen.V8Base.Part53
