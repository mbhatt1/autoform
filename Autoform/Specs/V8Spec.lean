import Autoform.Generated.V8BaseSample
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
deliberate: it makes each theorem independent of the other functions in the corpus. The module imported here is a
4-function extract of `v8/src/base` (`ast-V8BaseSample.json`), tracked so the repository
builds from a clean clone; the full 1,920-function render is a build product.
-/

namespace Autoform.V8Spec

open Autoform.Core Autoform.Generated.V8BaseSample

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
        bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, Env.set,
        execStmt, evalExpr, applyBinop, Val.truthy, Val.beq, C,
        -- `==`/`!=` now consults `binopNeedsHeap` first. On `.int` operands it is `false`
        -- and the heap-free path is taken, but `simp` has to be able to see that.
        binopNeedsHeap, Val.kind]

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

/-! ## The `rhs = -1` half

Until 2026-11-13 this was an open obligation, stated as a `Prop`-valued `def`. The
`rhs = 0` case reduces because `0` is a literal; `-1` is `Expr.unop "-" (lit 1)`, so the
guard's second disjunct goes through `applyUnop .cLike "-" (.int 1)`, i.e.
`numToE (NumConfig.c32Wrapv.neg 1)`, and `simp` with the numeric model unfolded did not
close it: the only `@[simp]` equation for C negation, `applyUnop_c_neg`, carries a
`Fits32 (-x)` side condition that the default discharger cannot settle because
`IntType.inRange` is not in the simp set. The fix is two concrete equations, each closed by
the kernel rather than by `simp`, which the main proof then rewrites with. -/

/-- `-1` is representable in 32 bits, so the wrapping C config negates `1` exactly.
Closed by `decide` (`NumResult` derives `DecidableEq`), the same way `Numeric.lean` pins
`c32Wrapv.mul 100000 100000`. -/
@[simp] theorem c32Wrapv_neg_one : NumConfig.c32Wrapv.neg 1 = .ok (-1) := by decide

/-- The unary-minus corollary at the `applyUnop` level: what the translated guard's
`Expr.unop "-" (Expr.lit (Lit.int 1))` evaluates to under the C dialect. -/
@[simp] theorem applyUnop_c_neg_one : applyUnop .cLike "-" (.int 1) = .val (.int (-1)) := by
  simp [applyUnop, numToE, Dialect.toNumConfig, c32Wrapv_neg_one]

/-- **The other half of the contract, for every `lhs`.**

`rhs = -1`: the guard's second disjunct fires and the function returns zero without
evaluating `lhs % rhs`, so `INT_MIN % -1` -- `#DE` on x86 -- is never reached. Same shape
as `signedMod32_zero_divisor`: universally quantified over `lhs` and over any fuel budget
at least 9. The script is the zero-divisor script plus the unary-minus equations above, the
`||` arm of `applyBinop` on the two concrete booleans the guard produces; `simp` decides
`-1 ≠ 0` as `Int`s itself, so the first disjunct's `==` is seen to be `false`. -/
theorem signedMod32_minus_one (lhs : Int) (k : Nat) :
    (applyFunc C (k+9) [] smod32 none [.int lhs, .int (-1)] []).2 = .val (.int 0) := by
  simp [applyFunc, smod32, f_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t_,
        bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, Env.set,
        execStmt, evalExpr, applyBinop, Val.truthy, Val.beq, C,
        binopNeedsHeap, Val.kind,
        -- The pieces the `rhs = 0` proof never needed: the unary minus on the literal
        -- `1`, the non-short-circuit `||` arm (its left disjunct is `false` here), and the
        -- dialect's answer to "is `a || b` a value or a boolean".
        applyUnop, numToE, Dialect.toNumConfig, Dialect.boolOpsAreValues,
        c32Wrapv_neg_one]

#audit_axioms signedMod32_minus_one
#audit_depends signedMod32_minus_one on f_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t_

end Autoform.V8Spec
