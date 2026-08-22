import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part41

theorem heappure_v8_base_Hasher___init_at_FUEL : ((dom_heappure_v8_base_Hasher___init).all (lawHeapPreserved C FUEL f_v8_base_Hasher___init__)) = true := by rfl

def ob_heappure_v8_base_Hasher___init : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_heappure_v8_base_Hasher___init).all (lawHeapPreserved C fuel f_v8_base_Hasher___init__)) = true


-- REFUTED by computation: `lawIdempotent` does not hold for `f_v8_base_Hasher___init__` over its own
-- domain at `FUEL`. The generator emitted a law its refutation pass should have
-- killed before emission; that is a defect in scripts/synth_specs.py.
theorem idempotent_v8_base_Hasher___init_refuted : ((dom_idempotent_v8_base_Hasher___init).all (lawIdempotent C FUEL f_v8_base_Hasher___init__)) = false := by rfl


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_heappure_v8_base_Hasher___init_1 rather than proved; see the module header for the measured cost.

end Autoform.SpecsGen.V8Base.Part41
