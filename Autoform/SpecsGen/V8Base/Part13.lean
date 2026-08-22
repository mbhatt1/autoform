import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part13

theorem uproj_v8_base_Win32MemoryMappedFile_memory_void____const :
    MRefines P "v8.base.Win32MemoryMappedFile.memory:void*()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "memory_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Win32MemoryMappedFile_memory_void____const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Win32MemoryMappedFile_memory_void____const_ "memory_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_Win32MemoryMappedFile_size_size_t___const :
    MRefines P "v8.base.Win32MemoryMappedFile.size:size_t()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "size_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Win32MemoryMappedFile_size_size_t___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Win32MemoryMappedFile_size_size_t___const_ "size_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uconst_n_FreeSubReservation_duplicate_1_bool_v8_base_AddressSpaceReservation :
    Refines P "v8.base.AddressSpaceReservation.FreeSubReservation<duplicate>1:bool(v8.base.AddressSpaceReservation)" 8
      (fun args => posRejected f_v8_base_AddressSpaceReservation_FreeSubReservation_duplicate_1_bool_v8_base_AddressSpaceReservation_ args = false)
      (fun _ => .ret (Val.bool true)) := by
  intro args hdom
  simp [posRejected, f_v8_base_AddressSpaceReservation_FreeSubReservation_duplicate_1_bool_v8_base_AddressSpaceReservation_, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_AddressSpaceReservation_FreeSubReservation_duplicate_1_bool_v8_base_AddressSpaceReservation_ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_AddressSpaceReservation_FreeSubReservation_duplicate_1_bool_v8_base_AddressSpaceReservation_, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_AddressSpaceReservation_FreeSubReservation_duplicate_1_bool_v8_base_AddressSpaceReservation_, ctxOf, P, hdom]

theorem uconst_v8_base_OS_ActivationFrameAlignment_duplicate_1_int :
    Refines P "v8.base.OS.ActivationFrameAlignment<duplicate>1:int()" 8
      (fun args => posRejected f_v8_base_OS_ActivationFrameAlignment_duplicate_1_int__ args = false)
      (fun _ => .ret (Val.int (8))) := by
  intro args hdom
  simp [posRejected, f_v8_base_OS_ActivationFrameAlignment_duplicate_1_int__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_OS_ActivationFrameAlignment_duplicate_1_int__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_ActivationFrameAlignment_duplicate_1_int__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_ActivationFrameAlignment_duplicate_1_int__, ctxOf, P, hdom]

theorem uconst_v8_base_OS_HasLazyCommits_duplicate_4_bool :
    Refines P "v8.base.OS.HasLazyCommits<duplicate>4:bool()" 8
      (fun args => posRejected f_v8_base_OS_HasLazyCommits_duplicate_4_bool__ args = false)
      (fun _ => .ret (Val.bool false)) := by
  intro args hdom
  simp [posRejected, f_v8_base_OS_HasLazyCommits_duplicate_4_bool__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_OS_HasLazyCommits_duplicate_4_bool__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_HasLazyCommits_duplicate_4_bool__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_HasLazyCommits_duplicate_4_bool__, ctxOf, P, hdom]


end Autoform.SpecsGen.V8Base.Part13
