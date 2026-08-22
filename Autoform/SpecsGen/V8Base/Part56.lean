import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part56

theorem identity_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_at_FUEL : ((dom_identity_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot).all (lawIdentity C FUEL f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem identity_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot : ∀ fuel, FUEL ≤ fuel → ((dom_identity_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot).all (lawIdentity C fuel f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_)) = true := by
  intro fuel hf
  exact all_transfer _ (gRun C FUEL f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_) (lawIdentity C FUEL f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_) (lawIdentity C fuel f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_)
    (fun c hgc hlc =>
      lawIdentity_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)


def ob_identity_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_identity_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot).all (lawIdentity C fuel f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_idempotent_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot rather than proved; see the module header for the measured cost.
theorem idempotent_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_at_FUEL : ((dom_idempotent_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot).all (lawIdempotent C FUEL f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem idempotent_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot : ∀ fuel, FUEL ≤ fuel → ((dom_idempotent_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot).all (lawIdempotent C fuel f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_)) = true := by
  intro fuel hf
  exact all_transfer _ (gIdem C FUEL f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_) (lawIdempotent C FUEL f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_) (lawIdempotent C fuel f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_)
    (fun c hgc hlc =>
      lawIdempotent_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)


def ob_idempotent_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_idempotent_alStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot).all (lawIdempotent C fuel f_v8_base_Stack_GetRealStackAddressForSlot_v8_base_Stack_StackSlot_v8_base_Stack_StackSlot_)) = true



end Autoform.SpecsGen.V8Base.Part56
