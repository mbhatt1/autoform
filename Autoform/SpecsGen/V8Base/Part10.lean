import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part10

theorem uconst_v8_base_OS_ActivationFrameAlignment_int :
    Refines P "v8.base.OS.ActivationFrameAlignment:int()" 8
      (fun args => posRejected f_v8_base_OS_ActivationFrameAlignment_int__ args = false)
      (fun _ => .ret (Val.int (16))) := by
  intro args hdom
  simp [posRejected, f_v8_base_OS_ActivationFrameAlignment_int__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_OS_ActivationFrameAlignment_int__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_ActivationFrameAlignment_int__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_ActivationFrameAlignment_int__, ctxOf, P, hdom]

theorem uconst_v8_base_OS_SetMemoryRegionName_duplicate_0_bool_void__size_t_char :
    Refines P "v8.base.OS.SetMemoryRegionName<duplicate>0:bool(void*,size_t,char*)" 8
      (fun args => posRejected f_v8_base_OS_SetMemoryRegionName_duplicate_0_bool_void__size_t_char__ args = false)
      (fun _ => .ret (Val.bool false)) := by
  intro args hdom
  simp [posRejected, f_v8_base_OS_SetMemoryRegionName_duplicate_0_bool_void__size_t_char__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_OS_SetMemoryRegionName_duplicate_0_bool_void__size_t_char__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_SetMemoryRegionName_duplicate_0_bool_void__size_t_char__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_SetMemoryRegionName_duplicate_0_bool_void__size_t_char__, ctxOf, P, hdom]

theorem uconst_v8_base_OS_SealPages_duplicate_1_bool_void__size_t :
    Refines P "v8.base.OS.SealPages<duplicate>1:bool(void*,size_t)" 8
      (fun args => posRejected f_v8_base_OS_SealPages_duplicate_1_bool_void__size_t_ args = false)
      (fun _ => .ret (Val.bool false)) := by
  intro args hdom
  simp [posRejected, f_v8_base_OS_SealPages_duplicate_1_bool_void__size_t_, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_OS_SealPages_duplicate_1_bool_void__size_t_ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_SealPages_duplicate_1_bool_void__size_t_, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_SealPages_duplicate_1_bool_void__size_t_, ctxOf, P, hdom]

theorem uconst_v8_base_OS_CanReserveAddressSpace_duplicate_0_bool :
    Refines P "v8.base.OS.CanReserveAddressSpace<duplicate>0:bool()" 8
      (fun args => posRejected f_v8_base_OS_CanReserveAddressSpace_duplicate_0_bool__ args = false)
      (fun _ => .ret (Val.bool true)) := by
  intro args hdom
  simp [posRejected, f_v8_base_OS_CanReserveAddressSpace_duplicate_0_bool__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_OS_CanReserveAddressSpace_duplicate_0_bool__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_CanReserveAddressSpace_duplicate_0_bool__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_CanReserveAddressSpace_duplicate_0_bool__, ctxOf, P, hdom]

theorem uconst_v8_base_OS_HasLazyCommits_duplicate_1_bool :
    Refines P "v8.base.OS.HasLazyCommits<duplicate>1:bool()" 8
      (fun args => posRejected f_v8_base_OS_HasLazyCommits_duplicate_1_bool__ args = false)
      (fun _ => .ret (Val.bool false)) := by
  intro args hdom
  simp [posRejected, f_v8_base_OS_HasLazyCommits_duplicate_1_bool__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_OS_HasLazyCommits_duplicate_1_bool__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_HasLazyCommits_duplicate_1_bool__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_OS_HasLazyCommits_duplicate_1_bool__, ctxOf, P, hdom]


end Autoform.SpecsGen.V8Base.Part10
