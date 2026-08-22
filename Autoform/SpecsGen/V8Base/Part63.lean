import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part63

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_charact_v8_base_SetFatalFunction_void_void rather than proved; see the module header for the measured cost.
theorem charact_v8_base_SetFatalFunction_void_void_at_FUEL : ((dom_charact_v8_base_SetFatalFunction_void_void).all (lawConform C FUEL f_v8_base_SetFatalFunction_void_void_)) = true := by rfl

def ob_charact_v8_base_SetFatalFunction_void_void : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_charact_v8_base_SetFatalFunction_void_void).all (lawConform C fuel f_v8_base_SetFatalFunction_void_void_)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_charact_v8_base_PosixInitializeCommon_void_char rather than proved; see the module header for the measured cost.
theorem charact_v8_base_PosixInitializeCommon_void_char_at_FUEL : ((dom_charact_v8_base_PosixInitializeCommon_void_char).all (lawConform C FUEL f_v8_base_PosixInitializeCommon_void_char__)) = true := by rfl


end Autoform.SpecsGen.V8Base.Part63
