import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part18

theorem commutes_v8_base_AddressRegion___init_1_at_FUEL : ((dom_commutes_v8_base_AddressRegion___init_1).all (lawCommutes C FUEL f_v8_base_AddressRegion___init__)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem commutes_v8_base_AddressRegion___init_1 : ∀ fuel, FUEL ≤ fuel → ((dom_commutes_v8_base_AddressRegion___init_1).all (lawCommutes C fuel f_v8_base_AddressRegion___init__)) = true := by
  intro fuel hf
  exact all_transfer _ (gComm C FUEL f_v8_base_AddressRegion___init__) (lawCommutes C FUEL f_v8_base_AddressRegion___init__) (lawCommutes C fuel f_v8_base_AddressRegion___init__)
    (fun c hgc hlc =>
      lawCommutes_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_AddressRegion___init__.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)


def ob_commutes_v8_base_AddressRegion___init_1 : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_commutes_v8_base_AddressRegion___init_1).all (lawCommutes C fuel f_v8_base_AddressRegion___init__)) = true


theorem uproj_v8_base_AddressRegion_begin_Address___const :
    MRefines P "v8.base.AddressRegion.begin:Address()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "address_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_AddressRegion_begin_Address___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_AddressRegion_begin_Address___const_ "address_" rfl rfl rfl rfl r [] rfl
      hmod

theorem uproj_v8_base_AddressRegion_size_size_t___const :
    MRefines P "v8.base.AddressRegion.size:size_t()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "size_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_AddressRegion_size_size_t___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_AddressRegion_size_size_t___const_ "size_" rfl rfl rfl rfl r [] rfl
      hmod

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_runs_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t rather than proved; see the module header for the measured cost.

end Autoform.SpecsGen.V8Base.Part18
