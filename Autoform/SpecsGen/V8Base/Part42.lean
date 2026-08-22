import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.V8Base
import Autoform.SpecsGen.V8Base.Base

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Autoform.Core Autoform.Refine Autoform.SpecsGen
open Autoform.SpecsGen.V8Base.Base
open Autoform.Generated.V8Base

namespace Autoform.SpecsGen.V8Base.Part42

theorem heappure_v8_base_Hasher___init_1_at_FUEL : ((dom_heappure_v8_base_Hasher___init_1).all (lawHeapPreserved C FUEL f_v8_base_Hasher___init__)) = true := by rfl

def ob_heappure_v8_base_Hasher___init_1 : Prop :=
  ∀ fuel, FUEL ≤ fuel → ((dom_heappure_v8_base_Hasher___init_1).all (lawHeapPreserved C fuel f_v8_base_Hasher___init__)) = true


-- REFUTED by computation: `lawIdempotent` does not hold for `f_v8_base_Hasher___init__` over its own
-- domain at `FUEL`. The generator emitted a law its refutation pass should have
-- killed before emission; that is a defect in scripts/synth_specs.py.
theorem idempotent_v8_base_Hasher___init_1_refuted : ((dom_idempotent_v8_base_Hasher___init_1).all (lawIdempotent C FUEL f_v8_base_Hasher___init__)) = false := by rfl


theorem uproj_v8_base_Hasher_hash_size_t___const :
    MRefines P "v8.base.Hasher.hash:size_t()<const>" 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r "hash_")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ f_v8_base_Hasher_hash_size_t___const_ rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h f_v8_base_Hasher_hash_size_t___const_ "hash_" rfl rfl rfl rfl r [] rfl
      hmod


end Autoform.SpecsGen.V8Base.Part42
