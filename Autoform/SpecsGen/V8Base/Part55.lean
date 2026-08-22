import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part55

theorem uproj_v8_base_Thread_Options_priority_v8_base_Thread_Priority___const :
    MRefines P "v8.base.Thread.Options.priority:v8.base.Thread.Priority()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "priority_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Thread_Options_priority_v8_base_Thread_Priority___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Thread_Options_priority_v8_base_Thread_Priority___const_ "priority_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_Thread_name_char____const :
    MRefines P "v8.base.Thread.name:char*()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "name_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Thread_name_char____const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Thread_name_char____const_ "name_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_Thread_data_v8_base_Thread_PlatformData :
    MRefines P "v8.base.Thread.data:v8.base.Thread.PlatformData*()" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "data_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Thread_data_v8_base_Thread_PlatformData___ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Thread_data_v8_base_Thread_PlatformData___ "data_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_Thread_priority_v8_base_Thread_Priority___const :
    MRefines P "v8.base.Thread.priority:v8.base.Thread.Priority()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "priority_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Thread_priority_v8_base_Thread_Priority___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Thread_priority_v8_base_Thread_Priority___const_ "priority_" rfl rfl rfl rfl r [] rfl
      hmod

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_identity_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot rather than proved; see the module header for the measured cost.

end Autoform.SpecsGen.V8Base.Part55
