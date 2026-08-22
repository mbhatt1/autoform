import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part14

theorem uproj_v8_base_PosixMemoryMappedFile_memory_duplicate_0_void____const :
    MRefines P "v8.base.PosixMemoryMappedFile.memory<duplicate>0:void*()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "memory_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_PosixMemoryMappedFile_memory_duplicate_0_void____const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_PosixMemoryMappedFile_memory_duplicate_0_void____const_ "memory_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_PosixMemoryMappedFile_size_duplicate_0_size_t___const :
    MRefines P "v8.base.PosixMemoryMappedFile.size<duplicate>0:size_t()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "size_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_PosixMemoryMappedFile_size_duplicate_0_size_t___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_PosixMemoryMappedFile_size_duplicate_0_size_t___const_ "size_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uconst_v8_base_TimeTicks_IsHighResolution_bool :
    Refines P "v8.base.TimeTicks.IsHighResolution:bool()" 8
      (fun args => posRejected f_v8_base_TimeTicks_IsHighResolution_bool__ args = false)
      (fun _ => .ret (Val.bool true)) := by
  intro args hdom
  simp [posRejected, f_v8_base_TimeTicks_IsHighResolution_bool__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_TimeTicks_IsHighResolution_bool__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_TimeTicks_IsHighResolution_bool__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_TimeTicks_IsHighResolution_bool__, ctxOf, P, hdom]

theorem uconst_v8_base_ThreadTicks_IsSupported_bool :
    Refines P "v8.base.ThreadTicks.IsSupported:bool()" 8
      (fun args => posRejected f_v8_base_ThreadTicks_IsSupported_bool__ args = false)
      (fun _ => .ret (Val.bool false)) := by
  intro args hdom
  simp [posRejected, f_v8_base_ThreadTicks_IsSupported_bool__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_ThreadTicks_IsSupported_bool__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_ThreadTicks_IsSupported_bool__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_ThreadTicks_IsSupported_bool__, ctxOf, P, hdom]

theorem uconst_v8_base_VirtualAddressSpacePageAllocator_SealPages_bool_void__size_t :
    Refines P "v8.base.VirtualAddressSpacePageAllocator.SealPages:bool(void*,size_t)" 8
      (fun args => posRejected f_v8_base_VirtualAddressSpacePageAllocator_SealPages_bool_void__size_t_ args = false)
      (fun _ => .ret (Val.bool false)) := by
  intro args hdom
  simp [posRejected, f_v8_base_VirtualAddressSpacePageAllocator_SealPages_bool_void__size_t_, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_VirtualAddressSpacePageAllocator_SealPages_bool_void__size_t_ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_VirtualAddressSpacePageAllocator_SealPages_bool_void__size_t_, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_VirtualAddressSpacePageAllocator_SealPages_bool_void__size_t_, ctxOf, P, hdom]


end Autoform.SpecsGen.V8Base.Part14
