import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part44

theorem runs_v8_base_hash32_uint32_t_uint32_t_refuted : ((dom_runs_v8_base_hash32_uint32_t_uint32_t).all (lawRuns C FUEL f_v8_base_hash32_uint32_t_uint32_t_)) = false := by rfl


-- REFUTED by computation: `lawReturns` does not hold for `f_v8_base_hash32_uint32_t_uint32_t_` over its own
-- domain at `FUEL`. The generator emitted a law its refutation pass should have
-- killed before emission; that is a defect in scripts/synth_specs.py.
theorem returns_v8_base_hash32_uint32_t_uint32_t_refuted : ((dom_returns_v8_base_hash32_uint32_t_uint32_t).all (lawReturns C FUEL f_v8_base_hash32_uint32_t_uint32_t_)) = false := by rfl


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_idempotent_v8_base_hash_value_size_t_unsigned_char rather than proved; see the module header for the measured cost.
theorem idempotent_v8_base_hash_value_size_t_unsigned_char_at_FUEL : ((dom_idempotent_v8_base_hash_value_size_t_unsigned_char).all (lawIdempotent C FUEL f_v8_base_hash_value_size_t_unsigned_char_)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem idempotent_v8_base_hash_value_size_t_unsigned_char : ∀ fuel, FUEL ≤ fuel → ((dom_idempotent_v8_base_hash_value_size_t_unsigned_char).all (lawIdempotent C fuel f_v8_base_hash_value_size_t_unsigned_char_)) = true := by
  intro fuel hf
  exact all_transfer _ (gIdem C FUEL f_v8_base_hash_value_size_t_unsigned_char_) (lawIdempotent C FUEL f_v8_base_hash_value_size_t_unsigned_char_) (lawIdempotent C fuel f_v8_base_hash_value_size_t_unsigned_char_)
    (fun c hgc hlc =>
      lawIdempotent_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_hash_value_size_t_unsigned_char_.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)



end Autoform.SpecsGen.V8Base.Part44
