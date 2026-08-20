import Autoform.Generated.V8Base
import Autoform.Harness.Audit

/-!
# Theorems about V8

The first theorems in this project about something other than `cachetools`.

The subject is `v8::base::bits::SignedMod32`, from `v8/src/base/bits.cc`, translated by
the pipeline with no holes. Its header documents a contract:

> `SignedMod32(lhs, rhs)` divides `|lhs|` by `|rhs|` and returns the remainder truncated
> to int32. **If either `|rhs|` is zero or `|lhs|` is minint and `|rhs|` is -1, it returns
> zero.**

That guard is not decoration: on x86 `INT_MIN % -1` raises `#DE`, the same trap as
division by zero. So the property worth proving is that the guard covers the trapping
inputs, for *every* `lhs` — not for a sample.

`SignedMod32` calls nothing, so the context below carries an empty function table. That is
deliberate: it makes each theorem independent of the other 1,734 functions in the module.
-/

namespace Autoform.V8Spec

open Autoform.Core Autoform.Generated

/-- The C dialect, with no other function in scope. -/
def C : Ctx := { dialect := .cLike, table := [], globals := 0 }

/-- `v8::base::bits::SignedMod32`, exactly as the transpiler emitted it. -/
abbrev smod32 := f_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t_

/-- **A theorem about V8, for every `lhs`.**

The `rhs = 0` half of the documented contract: the guard returns zero rather than dividing
by zero. Universally quantified over `lhs` and over any fuel budget at least 9, so it is
not a statement about sampled inputs or about one budget. -/
theorem signedMod32_zero_divisor (lhs : Int) (k : Nat) :
    (applyFunc C (k+9) [] smod32 none [.int lhs, .int 0] []).2 = .val (.int 0) := by
  simp [applyFunc, smod32, f_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t_,
        bindParams, Func.posParams, kwargsRejected, Env.set,
        execStmt, evalExpr, applyBinop, Val.truthy, Val.beq, C]

#audit_axioms signedMod32_zero_divisor
#audit_depends signedMod32_zero_divisor on f_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t_

/-! ## Pinned behaviour

`#guard_msgs` fails the build if the value changes, and — unlike `native_decide` — adds no
axiom. Each expected value is what the C source says, and the `INT_MIN` case is the one
that would trap natively. -/

private def run (a b : Int) : EResult :=
  (applyFunc C 200 [] smod32 none [.int a, .int b] []).2

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 0) -/
#guard_msgs in #eval run 7 0
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 0) -/
#guard_msgs in #eval run 7 (-1)
-- `INT_MIN % -1` — `#DE` on x86 without the guard.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 0) -/
#guard_msgs in #eval run (-2147483648) (-1)
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 1) -/
#guard_msgs in #eval run 7 3
-- C truncates toward zero, so this is `-1`, not `2`.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-1)) -/
#guard_msgs in #eval run (-7) 3

/-! ## Open obligation

Stated, not admitted — the convention this project uses everywhere. A `def` of a `Prop`
asserts nothing, which is why it is honest in a way `sorry` is not. -/

/-- The `rhs = -1` half of the contract, for every `lhs`. Not proved here.

The `rhs = 0` case reduces because `0` is a literal; `-1` is `Expr.unop "-" (lit 1)`, so
the guard's second disjunct goes through `NumConfig.c32Wrapv.neg`, and `simp` did not
close it with the numeric model unfolded. The behaviour IS pinned above at three
representative inputs including `INT_MIN`; what is missing is the universally quantified
proof, which is a different and stronger claim. -/
def ob_signedMod32_minus_one : Prop :=
  ∀ (lhs : Int) (k : Nat),
    (applyFunc C (k+9) [] smod32 none [.int lhs, .int (-1)] []).2 = .val (.int 0)

end Autoform.V8Spec
