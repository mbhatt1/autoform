import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part43

-- REFUTED by computation: `lawRuns` does not hold for `f_v8_base_hash64_uint64_t_uint64_t_` over its own
-- domain at `FUEL`. The generator emitted a law its refutation pass should have
-- killed before emission; that is a defect in scripts/synth_specs.py.
theorem runs_v8_base_hash64_uint64_t_uint64_t_refuted : ((dom_runs_v8_base_hash64_uint64_t_uint64_t).all (lawRuns C FUEL f_v8_base_hash64_uint64_t_uint64_t_)) = false := by rfl


-- REFUTED by computation: `lawReturns` does not hold for `f_v8_base_hash64_uint64_t_uint64_t_` over its own
-- domain at `FUEL`. The generator emitted a law its refutation pass should have
-- killed before emission; that is a defect in scripts/synth_specs.py.
theorem returns_v8_base_hash64_uint64_t_uint64_t_refuted : ((dom_returns_v8_base_hash64_uint64_t_uint64_t).all (lawReturns C FUEL f_v8_base_hash64_uint64_t_uint64_t_)) = false := by rfl


-- REFUTED by computation: `lawRuns` does not hold for `f_v8_base_hash32_uint32_t_uint32_t_` over its own
-- domain at `FUEL`. The generator emitted a law its refutation pass should have
-- killed before emission; that is a defect in scripts/synth_specs.py.

end Autoform.SpecsGen.V8Base.Part43
