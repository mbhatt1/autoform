import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part49

theorem idempotent_v8_base_internal_RangeCheck___init_refuted : ((dom_idempotent_v8_base_internal_RangeCheck___init).all (lawIdempotent C FUEL f_v8_base_internal_RangeCheck___init__)) = false := by rfl


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_commutes_v8_base_internal_RangeCheck___init rather than proved; see the module header for the measured cost.
theorem commutes_v8_base_internal_RangeCheck___init_at_FUEL : ((dom_commutes_v8_base_internal_RangeCheck___init).all (lawCommutes C FUEL f_v8_base_internal_RangeCheck___init__)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem commutes_v8_base_internal_RangeCheck___init : ∀ fuel, FUEL ≤ fuel → ((dom_commutes_v8_base_internal_RangeCheck___init).all (lawCommutes C fuel f_v8_base_internal_RangeCheck___init__)) = true := by
  intro fuel hf
  exact all_transfer _ (gComm C FUEL f_v8_base_internal_RangeCheck___init__) (lawCommutes C FUEL f_v8_base_internal_RangeCheck___init__) (lawCommutes C fuel f_v8_base_internal_RangeCheck___init__)
    (fun c hgc hlc =>
      lawCommutes_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_internal_RangeCheck___init__.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)


def ob_commutes_v8_base_internal_RangeCheck___init : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_commutes_v8_base_internal_RangeCheck___init).all (lawCommutes C fuel f_v8_base_internal_RangeCheck___init__)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_heappure_v8_base_internal_RangeCheck___init_1 rather than proved; see the module header for the measured cost.

end Autoform.SpecsGen.V8Base.Part49
