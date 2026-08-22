import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part8

-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_runs_v8_base_OS_Initialize_duplicate_0_void_char rather than proved; see the module header for the measured cost.
theorem runs_v8_base_OS_Initialize_duplicate_0_void_char_at_FUEL : ((dom_runs_v8_base_OS_Initialize_duplicate_0_void_char).all (lawRuns C FUEL f_v8_base_OS_Initialize_duplicate_0_void_char__)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem runs_v8_base_OS_Initialize_duplicate_0_void_char : ∀ fuel, FUEL ≤ fuel → ((dom_runs_v8_base_OS_Initialize_duplicate_0_void_char).all (lawRuns C fuel f_v8_base_OS_Initialize_duplicate_0_void_char__)) = true := by
  intro fuel hf
  exact all_transfer _ (gRun C FUEL f_v8_base_OS_Initialize_duplicate_0_void_char__) (lawRuns C FUEL f_v8_base_OS_Initialize_duplicate_0_void_char__) (lawRuns C fuel f_v8_base_OS_Initialize_duplicate_0_void_char__)
    (fun c hgc hlc =>
      lawRuns_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_OS_Initialize_duplicate_0_void_char__.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)


def ob_runs_v8_base_OS_Initialize_duplicate_0_void_char : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_runs_v8_base_OS_Initialize_duplicate_0_void_char).all (lawRuns C fuel f_v8_base_OS_Initialize_duplicate_0_void_char__)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_returns_v8_base_OS_Initialize_duplicate_0_void_char rather than proved; see the module header for the measured cost.
theorem returns_v8_base_OS_Initialize_duplicate_0_void_char_at_FUEL : ((dom_returns_v8_base_OS_Initialize_duplicate_0_void_char).all (lawReturns C FUEL f_v8_base_OS_Initialize_duplicate_0_void_char__)) = true := by rfl

-- Transported to every fuel budget at or above FUEL.
theorem returns_v8_base_OS_Initialize_duplicate_0_void_char : ∀ fuel, FUEL ≤ fuel → ((dom_returns_v8_base_OS_Initialize_duplicate_0_void_char).all (lawReturns C fuel f_v8_base_OS_Initialize_duplicate_0_void_char__)) = true := by
  intro fuel hf
  exact all_transfer _ (gRun C FUEL f_v8_base_OS_Initialize_duplicate_0_void_char__) (lawReturns C FUEL f_v8_base_OS_Initialize_duplicate_0_void_char__) (lawReturns C fuel f_v8_base_OS_Initialize_duplicate_0_void_char__)
    (fun c hgc hlc =>
      lawReturns_fuel_mono (hctx := C_tfFree) (hfn := (by rfl : tfFreeS f_v8_base_OS_Initialize_duplicate_0_void_char__.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)



end Autoform.SpecsGen.V8Base.Part8
