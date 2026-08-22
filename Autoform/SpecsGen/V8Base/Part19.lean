import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part19

theorem runs_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t_at_FUEL : ((dom_runs_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t).all (lawRuns C FUEL f_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t_)) = true := by rfl

def ob_runs_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_runs_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t).all (lawRuns C fuel f_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t_)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_returns_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t rather than proved; see the module header for the measured cost.
theorem returns_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t_at_FUEL : ((dom_returns_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t).all (lawReturns C FUEL f_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t_)) = true := by rfl

def ob_returns_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_returns_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t).all (lawReturns C fuel f_v8_UnsignedDiv32_uint32_t_uint32_t_uint32_t_)) = true



end Autoform.SpecsGen.V8Base.Part19
