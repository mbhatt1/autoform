import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part45

def ob_idempotent_v8_base_hash_value_size_t_unsigned_char : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_idempotent_v8_base_hash_value_size_t_unsigned_char).all (lawIdempotent C fuel f_v8_base_hash_value_size_t_unsigned_char_)) = true


-- Holds at `FUEL` by kernel computation. The forall-fuel transport is recorded as
-- ob_idempotent_v8_base_hash_value_size_t_shortunsigned rather than proved; see the module header for the measured cost.
theorem idempotent_v8_base_hash_value_size_t_shortunsigned_at_FUEL : ((dom_idempotent_v8_base_hash_value_size_t_shortunsigned).all (lawIdempotent C FUEL f_v8_base_hash_value_size_t_shortunsigned_)) = true := by rfl

def ob_idempotent_v8_base_hash_value_size_t_shortunsigned : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_idempotent_v8_base_hash_value_size_t_shortunsigned).all (lawIdempotent C fuel f_v8_base_hash_value_size_t_shortunsigned_)) = true


theorem uproj_v8_base_DiyFp_f_uint64_t___const :
    MRefines P "v8.base.DiyFp.f:uint64_t()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "f_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_DiyFp_f_uint64_t___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_DiyFp_f_uint64_t___const_ "f_" rfl rfl rfl rfl r [] rfl
      hmod


end Autoform.SpecsGen.V8Base.Part45
