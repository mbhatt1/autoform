import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part66

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_charact_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t rather than proved; see the module header for the measured cost.
theorem charact_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t_at_FUEL : ((dom_charact_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t).all (lawConform C FUEL f_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t_)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem charact_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t : ∀ fuel, FUEL ≤ fuel → ((dom_charact_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t).all (lawConform C fuel f_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t_)) = true := by
  intro fuel hf
  exact all_transfer _ (gRunObs C FUEL f_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t_) (lawConform C FUEL f_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t_) (lawConform C fuel f_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t_)
    (fun c hgc hlc =>
      lawConform_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t_.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)


def ob_charact_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_charact_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t).all (lawConform C fuel f_v8_UnsignedDiv64_uint64_t_uint64_t_uint64_t_)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_charact_v8_UnsignedMod32_uint32_t_uint32_t_uint32_t rather than proved; see the module header for the measured cost.
theorem charact_v8_UnsignedMod32_uint32_t_uint32_t_uint32_t_at_FUEL : ((dom_charact_v8_UnsignedMod32_uint32_t_uint32_t_uint32_t).all (lawConform C FUEL f_v8_UnsignedMod32_uint32_t_uint32_t_uint32_t_)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem charact_v8_UnsignedMod32_uint32_t_uint32_t_uint32_t : ∀ fuel, FUEL ≤ fuel → ((dom_charact_v8_UnsignedMod32_uint32_t_uint32_t_uint32_t).all (lawConform C fuel f_v8_UnsignedMod32_uint32_t_uint32_t_uint32_t_)) = true := by
  intro fuel hf
  exact all_transfer _ (gRunObs C FUEL f_v8_UnsignedMod32_uint32_t_uint32_t_uint32_t_) (lawConform C FUEL f_v8_UnsignedMod32_uint32_t_uint32_t_uint32_t_) (lawConform C fuel f_v8_UnsignedMod32_uint32_t_uint32_t_uint32_t_)
    (fun c hgc hlc =>
      lawConform_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_UnsignedMod32_uint32_t_uint32_t_uint32_t_.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)



end Autoform.SpecsGen.V8Base.Part66
