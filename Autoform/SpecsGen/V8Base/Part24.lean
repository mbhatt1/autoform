import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part24

def ob_runs_v8_WraparoundAdd32_int32_t_int32_t_int32_t : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_runs_v8_WraparoundAdd32_int32_t_int32_t_int32_t).all (lawRuns C fuel f_v8_WraparoundAdd32_int32_t_int32_t_int32_t_)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_returns_v8_WraparoundAdd32_int32_t_int32_t_int32_t rather than proved; see the module header for the measured cost.
theorem returns_v8_WraparoundAdd32_int32_t_int32_t_int32_t_at_FUEL : ((dom_returns_v8_WraparoundAdd32_int32_t_int32_t_int32_t).all (lawReturns C FUEL f_v8_WraparoundAdd32_int32_t_int32_t_int32_t_)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem returns_v8_WraparoundAdd32_int32_t_int32_t_int32_t : ∀ fuel, FUEL ≤ fuel → ((dom_returns_v8_WraparoundAdd32_int32_t_int32_t_int32_t).all (lawReturns C fuel f_v8_WraparoundAdd32_int32_t_int32_t_int32_t_)) = true := by
  intro fuel hf
  exact all_transfer _ (gRun C FUEL f_v8_WraparoundAdd32_int32_t_int32_t_int32_t_) (lawReturns C FUEL f_v8_WraparoundAdd32_int32_t_int32_t_int32_t_) (lawReturns C fuel f_v8_WraparoundAdd32_int32_t_int32_t_int32_t_)
    (fun c hgc hlc =>
      lawReturns_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_WraparoundAdd32_int32_t_int32_t_int32_t_.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)


def ob_returns_v8_WraparoundAdd32_int32_t_int32_t_int32_t : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_returns_v8_WraparoundAdd32_int32_t_int32_t_int32_t).all (lawReturns C fuel f_v8_WraparoundAdd32_int32_t_int32_t_int32_t_)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_commutes_v8_WraparoundAdd32_int32_t_int32_t_int32_t rather than proved; see the module header for the measured cost.

end Autoform.SpecsGen.V8Base.Part24
