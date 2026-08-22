import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part72

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_charact_v8_base_internal_RangeCheck___init rather than proved; see the module header for the measured cost.
-- REFUTED by kernel computation: this law is FALSE over its own domain.
-- scripts/synth_specs.py emitted it; its refutation pass should have killed
-- it before emission. Recorded, not deleted.
theorem charact_v8_base_internal_RangeCheck___init_refuted : ((dom_charact_v8_base_internal_RangeCheck___init).all (lawConform C FUEL f_v8_base_internal_RangeCheck___init__)) = false := by rfl

def ob_charact_v8_base_internal_RangeCheck___init : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_charact_v8_base_internal_RangeCheck___init).all (lawConform C fuel f_v8_base_internal_RangeCheck___init__)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_charact_v8_base_MulWithWraparound_int16_t_int16_t_int16_t rather than proved; see the module header for the measured cost.
theorem charact_v8_base_MulWithWraparound_int16_t_int16_t_int16_t_at_FUEL : ((dom_charact_v8_base_MulWithWraparound_int16_t_int16_t_int16_t).all (lawConform C FUEL f_v8_base_MulWithWraparound_int16_t_int16_t_int16_t_)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem charact_v8_base_MulWithWraparound_int16_t_int16_t_int16_t : ∀ fuel, FUEL ≤ fuel → ((dom_charact_v8_base_MulWithWraparound_int16_t_int16_t_int16_t).all (lawConform C fuel f_v8_base_MulWithWraparound_int16_t_int16_t_int16_t_)) = true := by
  intro fuel hf
  exact all_transfer _ (gRunObs C FUEL f_v8_base_MulWithWraparound_int16_t_int16_t_int16_t_) (lawConform C FUEL f_v8_base_MulWithWraparound_int16_t_int16_t_int16_t_) (lawConform C fuel f_v8_base_MulWithWraparound_int16_t_int16_t_int16_t_)
    (fun c hgc hlc =>
      lawConform_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_MulWithWraparound_int16_t_int16_t_int16_t_.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)



end Autoform.SpecsGen.V8Base.Part72
