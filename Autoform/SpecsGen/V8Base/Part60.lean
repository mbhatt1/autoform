import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part60

theorem uproj_v8_base_Vector_cbegin_ANY___const :
    MRefines P "v8.base.Vector.cbegin:ANY()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "start_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Vector_cbegin_ANY___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Vector_cbegin_ANY___const_ "start_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_Vector_data_ANY___const :
    MRefines P "v8.base.Vector.data:ANY()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "start_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Vector_data_ANY___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Vector_data_ANY___const_ "start_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_OwnedVector_size_size_t___const :
    MRefines P "v8.base.OwnedVector.size:size_t()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "length_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_OwnedVector_size_size_t___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_OwnedVector_size_size_t___const_ "length_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_EmbeddedVector_size_size_t___const :
    MRefines P "v8.base.EmbeddedVector.size:size_t()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "length_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_EmbeddedVector_size_size_t___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_EmbeddedVector_size_size_t___const_ "length_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uconst_v8_base_VirtualAddressSpace_SetName_bool_std_string :
    Refines P "v8.base.VirtualAddressSpace.SetName:bool(std.string&)" 8
      (fun args => posRejected f_v8_base_VirtualAddressSpace_SetName_bool_std_string__ args = false)
      (fun _ => .ret (Val.bool false)) := by
  intro args hdom
  simp [posRejected, f_v8_base_VirtualAddressSpace_SetName_bool_std_string__, Func.posParams] at hdom
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_v8_base_VirtualAddressSpace_SetName_bool_std_string__ rfl]
  first
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_VirtualAddressSpace_SetName_bool_std_string__, ctxOf, P, hdom, Nat.not_lt.mpr hdom]
    | simp [applyFunc, execStmt, evalExpr, Env.set, f_v8_base_VirtualAddressSpace_SetName_bool_std_string__, ctxOf, P, hdom]


end Autoform.SpecsGen.V8Base.Part60
