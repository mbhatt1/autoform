import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part71

theorem charact_v8_base_hash_value_size_t_shortunsigned_at_FUEL : ((dom_charact_v8_base_hash_value_size_t_shortunsigned).all (lawConform C FUEL f_v8_base_hash_value_size_t_shortunsigned_)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem charact_v8_base_hash_value_size_t_shortunsigned : ∀ fuel, FUEL ≤ fuel → ((dom_charact_v8_base_hash_value_size_t_shortunsigned).all (lawConform C fuel f_v8_base_hash_value_size_t_shortunsigned_)) = true := by
  intro fuel hf
  exact all_transfer _ (gRunObs C FUEL f_v8_base_hash_value_size_t_shortunsigned_) (lawConform C FUEL f_v8_base_hash_value_size_t_shortunsigned_) (lawConform C fuel f_v8_base_hash_value_size_t_shortunsigned_)
    (fun c hgc hlc =>
      lawConform_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_hash_value_size_t_shortunsigned_.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)


def ob_charact_v8_base_hash_value_size_t_shortunsigned : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_charact_v8_base_hash_value_size_t_shortunsigned).all (lawConform C fuel f_v8_base_hash_value_size_t_shortunsigned_)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_charact_v8_base_internal_MakeStrictNum_StrictNumeric_T rather than proved; see the module header for the measured cost.
theorem charact_v8_base_internal_MakeStrictNum_StrictNumeric_T_at_FUEL : ((dom_charact_v8_base_internal_MakeStrictNum_StrictNumeric_T).all (lawConform C FUEL f_v8_base_internal_MakeStrictNum_StrictNumeric_T_)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem charact_v8_base_internal_MakeStrictNum_StrictNumeric_T : ∀ fuel, FUEL ≤ fuel → ((dom_charact_v8_base_internal_MakeStrictNum_StrictNumeric_T).all (lawConform C fuel f_v8_base_internal_MakeStrictNum_StrictNumeric_T_)) = true := by
  intro fuel hf
  exact all_transfer _ (gRunObs C FUEL f_v8_base_internal_MakeStrictNum_StrictNumeric_T_) (lawConform C FUEL f_v8_base_internal_MakeStrictNum_StrictNumeric_T_) (lawConform C fuel f_v8_base_internal_MakeStrictNum_StrictNumeric_T_)
    (fun c hgc hlc =>
      lawConform_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_internal_MakeStrictNum_StrictNumeric_T_.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)


def ob_charact_v8_base_internal_MakeStrictNum_StrictNumeric_T : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_charact_v8_base_internal_MakeStrictNum_StrictNumeric_T).all (lawConform C fuel f_v8_base_internal_MakeStrictNum_StrictNumeric_T_)) = true



end Autoform.SpecsGen.V8Base.Part71
