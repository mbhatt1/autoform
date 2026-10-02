import Autoform.Generated.CAddr

/-!
# The C address model, on the exported program

`tests/c_address/addr.c`, exported by `cartographer/export_ast.sc` and rendered by
`cartographer/render_lean.py` into `Autoform.Generated.CAddr`, run through the Core
interpreter. Every defined value below is what `cc -O0` printed on x86-64 for the same
call; `scripts/differential.py ast-CAddr.json tests/c_address CAddr` compares the same
functions on random inputs. The holes are the cases C does not define: there the model
must refuse, whatever a native build happens to print.

Before the address model, 9 of these 14 functions were static holes
(`op:addressOf:element:scalar`, `cstr:pointer-arith`, `cstr:address-equality`,
`op:postIncrement:pointer`): every pointer here is loaded from a struct field, so the
exporter could not prove where it pointed.
-/

namespace Autoform.AddressSpec

open Autoform.Core

private def run (f : String) (args : List Int) : EResult :=
  runFunc Autoform.Generated.CAddr.program 400 f (args.map Val.int)

-- Same-block ordering over a local array, one past the end allowed. `cc`: 6, 36.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 6) -/
#guard_msgs in #eval run "sum_until" [3]
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 36) -/
#guard_msgs in #eval run "sum_until" [8]

-- `&b->a[i]` on a pointer of unknown provenance, then compared. `cc`: -1, 1, 0, 1.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-1)) -/
#guard_msgs in #eval run "field_order" [2, 5]
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 1) -/
#guard_msgs in #eval run "field_order" [5, 2]
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 0) -/
#guard_msgs in #eval run "field_order" [4, 4]
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 1) -/
#guard_msgs in #eval run "field_order" [8, 0]

-- Equality, and a walk with `p++` up to an end pointer. `cc`: 1, 0, 5, 0.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 1) -/
#guard_msgs in #eval run "field_eq" [3, 3]
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 0) -/
#guard_msgs in #eval run "field_eq" [3, 4]
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 5) -/
#guard_msgs in #eval run "walk_span" [2, 7]
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 0) -/
#guard_msgs in #eval run "walk_span" [7, 2]

-- Pointer difference and pointer minus integer. `cc`: 5, -5, 1.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 5) -/
#guard_msgs in #eval run "gap" [1, 6]
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-5)) -/
#guard_msgs in #eval run "gap" [6, 1]
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 1) -/
#guard_msgs in #eval run "back_eq" [6, 2]

-- Undefined and unspecified: holes, never values.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-1)) -/
#guard_msgs in #eval run "oob_order" [3]
/-- info: Autoform.Core.EResult.hole "ub:ptr-arith-out-of-bounds" -/
#guard_msgs in #eval run "oob_order" [5]
/-- info: Autoform.Core.EResult.hole "ub:ptr-arith-out-of-bounds" -/
#guard_msgs in #eval run "oob_order" [-1]
/-- info: Autoform.Core.EResult.hole "ptr:eq-one-past-unspecified" -/
#guard_msgs in #eval run "past_end" [0]
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 0) -/
#guard_msgs in #eval run "past_end" [1]

/-- The defining cases as a kernel-checked statement, not only `#eval`. -/
theorem address_model_agrees_with_cc :
    run "field_order" [2, 5] = .val (.int (-1)) ∧
    run "gap" [6, 1] = .val (.int (-5)) ∧
    run "oob_order" [5] = .hole "ub:ptr-arith-out-of-bounds" ∧
    run "past_end" [0] = .hole "ptr:eq-one-past-unspecified" := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

end Autoform.AddressSpec
