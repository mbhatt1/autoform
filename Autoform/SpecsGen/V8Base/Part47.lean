import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part47

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_idempotent_v8_base_internal_MakeStrictNum_StrictNumeric_T rather than proved; see the module header for the measured cost.
theorem idempotent_v8_base_internal_MakeStrictNum_StrictNumeric_T_at_FUEL : ((dom_idempotent_v8_base_internal_MakeStrictNum_StrictNumeric_T).all (lawIdempotent C FUEL f_v8_base_internal_MakeStrictNum_StrictNumeric_T_)) = true := by rfl

def ob_idempotent_v8_base_internal_MakeStrictNum_StrictNumeric_T : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_idempotent_v8_base_internal_MakeStrictNum_StrictNumeric_T).all (lawIdempotent C fuel f_v8_base_internal_MakeStrictNum_StrictNumeric_T_)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_involutive_v8_base_internal_MakeStrictNum_StrictNumeric_T rather than proved; see the module header for the measured cost.
theorem involutive_v8_base_internal_MakeStrictNum_StrictNumeric_T_at_FUEL : ((dom_involutive_v8_base_internal_MakeStrictNum_StrictNumeric_T).all (lawInvolutive C FUEL f_v8_base_internal_MakeStrictNum_StrictNumeric_T_)) = true := by rfl


end Autoform.SpecsGen.V8Base.Part47
