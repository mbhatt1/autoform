import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part54

theorem uconst_v8_base_OS_IsRemapPageSupported_bool :
    Refines P "v8.base.OS.IsRemapPageSupported:bool()" 8
      (fun args => posRejected f_v8_base_OS_IsRemapPageSupported_bool__ args = false)
      (fun _ => .ret (Val.bool false)) := by
  intro args hdom
  simp [posRejected, f_v8_base_OS_IsRemapPageSupported_bool__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_OS_IsRemapPageSupported_bool__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_IsRemapPageSupported_bool__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_IsRemapPageSupported_bool__, ctxOf, P, hdom]

theorem uproj_v8_base_AddressSpaceReservation_base_void____const :
    MRefines P "v8.base.AddressSpaceReservation.base:void*()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "base_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_AddressSpaceReservation_base_void____const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_AddressSpaceReservation_base_void____const_ "base_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_AddressSpaceReservation_size_size_t___const :
    MRefines P "v8.base.AddressSpaceReservation.size:size_t()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "size_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_AddressSpaceReservation_size_size_t___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_AddressSpaceReservation_size_size_t___const_ "size_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_Thread_Options_name_char____const :
    MRefines P "v8.base.Thread.Options.name:char*()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "name_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Thread_Options_name_char____const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Thread_Options_name_char____const_ "name_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_Thread_Options_stack_size_int___const :
    MRefines P "v8.base.Thread.Options.stack_size:int()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "stack_size_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Thread_Options_stack_size_int___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Thread_Options_stack_size_int___const_ "stack_size_" rfl rfl rfl rfl r [] rfl
      hmod


end Autoform.SpecsGen.V8Base.Part54
