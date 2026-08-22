import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part17

theorem heappure_v8_base_AddressRegion___init_1_at_FUEL : ((dom_heappure_v8_base_AddressRegion___init_1).all (lawHeapPreserved C FUEL f_v8_base_AddressRegion___init__)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem heappure_v8_base_AddressRegion___init_1 : ∀ fuel, FUEL ≤ fuel → ((dom_heappure_v8_base_AddressRegion___init_1).all (lawHeapPreserved C fuel f_v8_base_AddressRegion___init__)) = true := by
  intro fuel hf
  exact all_transfer _ (gRun C FUEL f_v8_base_AddressRegion___init__) (lawHeapPreserved C FUEL f_v8_base_AddressRegion___init__) (lawHeapPreserved C fuel f_v8_base_AddressRegion___init__)
    (fun c hgc hlc =>
      lawHeapPreserved_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_AddressRegion___init__.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)


def ob_heappure_v8_base_AddressRegion___init_1 : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_heappure_v8_base_AddressRegion___init_1).all (lawHeapPreserved C fuel f_v8_base_AddressRegion___init__)) = true


-- REFUTED by computation: `lawIdempotent` does not hold for `f_v8_base_AddressRegion___init__` over its own
-- domain at `FUEL`. The generator emitted a law its refutation pass should have
-- killed before emission; that is a defect in scripts/synth_specs.py.
theorem idempotent_v8_base_AddressRegion___init_1_refuted : ((dom_idempotent_v8_base_AddressRegion___init_1).all (lawIdempotent C FUEL f_v8_base_AddressRegion___init__)) = false := by rfl


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_commutes_v8_base_AddressRegion___init_1 rather than proved; see the module header for the measured cost.

end Autoform.SpecsGen.V8Base.Part17
