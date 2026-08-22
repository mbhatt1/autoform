import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part3

theorem returns_v8_base_bits_SignedMod64_int64_t_int64_t_int64_t_at_FUEL : ((dom_returns_v8_base_bits_SignedMod64_int64_t_int64_t_int64_t).all (lawReturns C FUEL f_v8_base_bits_SignedMod64_int64_t_int64_t_int64_t_)) = true := by rfl

def ob_returns_v8_base_bits_SignedMod64_int64_t_int64_t_int64_t : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_returns_v8_base_bits_SignedMod64_int64_t_int64_t_int64_t).all (lawReturns C fuel f_v8_base_bits_SignedMod64_int64_t_int64_t_int64_t_)) = true


theorem uconst_v8_base_debug_EnableInProcessStackDumping_duplicate_0_bool :
    Refines P "v8.base.debug.EnableInProcessStackDumping<duplicate>0:bool()" 8
      (fun args => posRejected f_v8_base_debug_EnableInProcessStackDumping_duplicate_0_bool__ args = false)
      (fun _ => .ret (Val.bool false)) := by
  intro args hdom
  simp [posRejected, f_v8_base_debug_EnableInProcessStackDumping_duplicate_0_bool__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_debug_EnableInProcessStackDumping_duplicate_0_bool__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_debug_EnableInProcessStackDumping_duplicate_0_bool__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_debug_EnableInProcessStackDumping_duplicate_0_bool__, ctxOf, P, hdom]

theorem uconst_v8_base_debug_BacktraceOutputHandler_OutputFileDescriptor_int___const :
    Refines P "v8.base.debug.BacktraceOutputHandler.OutputFileDescriptor:int()<const>" 8
      (fun args => posRejected f_v8_base_debug_BacktraceOutputHandler_OutputFileDescriptor_int___const_ args = false)
      (fun _ => .ret (Val.int (0))) := by
  intro args hdom
  simp [posRejected, f_v8_base_debug_BacktraceOutputHandler_OutputFileDescriptor_int___const_, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_debug_BacktraceOutputHandler_OutputFileDescriptor_int___const_ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_debug_BacktraceOutputHandler_OutputFileDescriptor_int___const_, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_debug_BacktraceOutputHandler_OutputFileDescriptor_int___const_, ctxOf, P, hdom]

theorem uconst_v8_base_EmulatedVirtualAddressSubspace_CanAllocateSubspaces_bool :
    Refines P "v8.base.EmulatedVirtualAddressSubspace.CanAllocateSubspaces:bool()" 8
      (fun args => posRejected f_v8_base_EmulatedVirtualAddressSubspace_CanAllocateSubspaces_bool__ args = false)
      (fun _ => .ret (Val.bool false)) := by
  intro args hdom
  simp [posRejected, f_v8_base_EmulatedVirtualAddressSubspace_CanAllocateSubspaces_bool__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_EmulatedVirtualAddressSubspace_CanAllocateSubspaces_bool__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_EmulatedVirtualAddressSubspace_CanAllocateSubspaces_bool__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_EmulatedVirtualAddressSubspace_CanAllocateSubspaces_bool__, ctxOf, P, hdom]


end Autoform.SpecsGen.V8Base.Part3
