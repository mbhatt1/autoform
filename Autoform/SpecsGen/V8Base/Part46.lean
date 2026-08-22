import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part46

theorem uproj_v8_base_DiyFp_e_int___const :
    MRefines P "v8.base.DiyFp.e:int()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "e_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_DiyFp_e_int___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_DiyFp_e_int___const_ "e_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_Double_AsUint64_uint64_t___const :
    MRefines P "v8.base.Double.AsUint64:uint64_t()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "d64_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Double_AsUint64_uint64_t___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Double_AsUint64_uint64_t___const_ "d64_" rfl rfl rfl rfl r [] rfl
      hmod

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_identity_v8_base_internal_MakeStrictNum_StrictNumeric_T rather than proved; see the module header for the measured cost.
theorem identity_v8_base_internal_MakeStrictNum_StrictNumeric_T_at_FUEL : ((dom_identity_v8_base_internal_MakeStrictNum_StrictNumeric_T).all (lawIdentity C FUEL f_v8_base_internal_MakeStrictNum_StrictNumeric_T_)) = true := by rfl

def ob_identity_v8_base_internal_MakeStrictNum_StrictNumeric_T : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_identity_v8_base_internal_MakeStrictNum_StrictNumeric_T).all (lawIdentity C fuel f_v8_base_internal_MakeStrictNum_StrictNumeric_T_)) = true



end Autoform.SpecsGen.V8Base.Part46
