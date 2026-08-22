import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part15

theorem uproj_v8_base_VirtualAddressSubspace_ActiveMemoryProtectionKey_optional :
    MRefines P "v8.base.VirtualAddressSubspace.ActiveMemoryProtectionKey:optional()" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "pkey_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_VirtualAddressSubspace_ActiveMemoryProtectionKey_optional__ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_VirtualAddressSubspace_ActiveMemoryProtectionKey_optional__ "pkey_" rfl rfl rfl rfl r [] rfl
      hmod

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_heappure_v8_base_AddressRegion___init rather than proved; see the module header for the measured cost.
theorem heappure_v8_base_AddressRegion___init_at_FUEL : ((dom_heappure_v8_base_AddressRegion___init).all (lawHeapPreserved C FUEL f_v8_base_AddressRegion___init__)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem heappure_v8_base_AddressRegion___init : ∀ fuel, FUEL ≤ fuel → ((dom_heappure_v8_base_AddressRegion___init).all (lawHeapPreserved C fuel f_v8_base_AddressRegion___init__)) = true := by
  intro fuel hf
  exact all_transfer _ (gRun C FUEL f_v8_base_AddressRegion___init__) (lawHeapPreserved C FUEL f_v8_base_AddressRegion___init__) (lawHeapPreserved C fuel f_v8_base_AddressRegion___init__)
    (fun c hgc hlc =>
      lawHeapPreserved_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_AddressRegion___init__.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)


def ob_heappure_v8_base_AddressRegion___init : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_heappure_v8_base_AddressRegion___init).all (lawHeapPreserved C fuel f_v8_base_AddressRegion___init__)) = true


-- REFUTED by computation: `lawIdempotent` does not hold for `f_v8_base_AddressRegion___init__` over its own
-- domain at `FUEL`. The generator emitted a law its refutation pass should have
-- killed before emission; that is a defect in scripts/synth_specs.py.

end Autoform.SpecsGen.V8Base.Part15
