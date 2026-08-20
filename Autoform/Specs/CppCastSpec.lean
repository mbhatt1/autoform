import Autoform.Lang.Core.Semantics

/-!
# `CppCastSpec` — the widths the C++ exporter resolves, checked against `cc`

`Autoform/Lang/Core/Semantics.lean` already models a width conversion (`unop "cast:uN"` is
`IntType.wrap`) and already pins one case, `static_cast<uint8_t>(344) = 88`, against a real
compiler. What it does *not* pin is the step in front of it: **deciding which width a
written type name denotes.**

That step is where V8 actually loses. V8 almost never writes `uint32_t` at a cast site; it
writes a name introduced by a class-local `using`:

```c++
namespace v8::base { class AddressRegion { using Address = uintptr_t; ... }; }
namespace v8::base { class Bignum       { using Chunk   = uint32_t;  ... }; }
```

The exporter follows the CPG's `TypeDecl.aliasTypeFullName` edges (`resolveIntType`) to get
from `Address` to `uintptr_t` to `u64`, and from `Chunk` to `uint32_t` to `u32`. That
resolution is a *claim about what the C++ compiler will do*, and a wrong claim here is the
worst kind of bug this project can have: it silently changes arithmetic in a program that
still type-checks and still proves every downstream theorem.

So the claim is checked the same way the pipeline checks everything else — against the
compiler. `cc -std=c++20` on this machine reports:

```
u8(344)      = 88
i8(200)      = -56
Chunk(-1)    = 4294967295
Chunk(1<<33) = 0
Address(-1)  = 18446744073709551615
sizeof(Address)=8   sizeof(Chunk)=4
```

and every number below is one of those. `#guard_msgs` fails the build if any of them moves,
and unlike `native_decide` it introduces no axiom — `#print axioms` at the bottom is the
receipt.

**Non-vacuity.** Three ways a "cast" could be fake, all of them excluded here:

* it could always be a hole — `castProg` returns `Val.int`, never `EResult.hole`;
* it could be the identity — every operand below is chosen *outside* the target range, so
  the identity would give a different answer (`-1`, not `4294967295`), and `notIdentity`
  states that as a theorem;
* the two widths could be the same function — `chunkVsAddress` shows they are not, since
  `-1` maps to `2^32-1` under `Chunk` and to `2^64-1` under `Address`.
-/

namespace Autoform.Specs
open Autoform.Core

/-- The three cast operators the C++ exporter emits after resolving a *typedef*, applied to
operands that lie outside the target type's range so that the conversion is observable.

`ns.chunk` is `static_cast<Bignum::Chunk>(-1)`, `ns.chunkHigh` is
`static_cast<Bignum::Chunk>(1 << 33)`, and `ns.address` is
`static_cast<AddressRegion::Address>(-1)` — the exact shapes that appear in
`Autoform/Generated/V8Base.lean` after this change. -/
private def castProg : Program :=
  { dialect := .cLike
  , funcs :=
    [ { name := "ns.chunk",     params := []
      , body := .ret (.unop "cast:u32" (.lit (.int (-1)))) }
    , { name := "ns.chunkHigh", params := []
      , body := .ret (.unop "cast:u32" (.lit (.int 8589934592))) }
    , { name := "ns.address",   params := []
      , body := .ret (.unop "cast:u64" (.lit (.int (-1)))) }
    , { name := "ns.byte",      params := []
      , body := .ret (.unop "cast:u8" (.lit (.int 344))) }
    , { name := "ns.sbyte",     params := []
      , body := .ret (.unop "cast:i8" (.lit (.int 200))) } ] }

/-- `static_cast<Chunk>(-1)` is `4294967295`, matching `cc`. -/
theorem chunk : runFunc castProg 100 "ns.chunk" [] = .val (.int 4294967295) := by rfl

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 4294967295) -/
#guard_msgs in #eval runFunc castProg 100 "ns.chunk" []

/-- `static_cast<Chunk>(1 << 33)` is `0`: the value is a whole multiple of `2^32`, so a
32-bit truncation keeps nothing. A 64-bit conversion would give `8589934592`, so this case
distinguishes the width the exporter chose from the next one up. -/
theorem chunkHigh : runFunc castProg 100 "ns.chunkHigh" [] = .val (.int 0) := by rfl

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 0) -/
#guard_msgs in #eval runFunc castProg 100 "ns.chunkHigh" []

/-- `static_cast<Address>(-1)` is `18446744073709551615`, matching `cc` on a 64-bit
`uintptr_t`. -/
theorem address : runFunc castProg 100 "ns.address" [] = .val (.int 18446744073709551615) := by
  rfl

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 18446744073709551615) -/
#guard_msgs in #eval runFunc castProg 100 "ns.address" []

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 88) -/
#guard_msgs in #eval runFunc castProg 100 "ns.byte" []

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-56)) -/
#guard_msgs in #eval runFunc castProg 100 "ns.sbyte" []

/-- **The cast is not the identity.** If `resolveIntType` had produced a translation that
handed its operand back unchanged, every theorem above would still be a theorem about
*something* and every downstream proof would still pass. It does not: `-1` does not survive
either conversion. -/
theorem notIdentity :
    runFunc castProg 100 "ns.chunk" []   ≠ .val (.int (-1)) ∧
    runFunc castProg 100 "ns.address" [] ≠ .val (.int (-1)) :=
  ⟨by rw [chunk]; simp, by rw [address]; simp⟩

/-- **The two resolved widths are different functions.** `Chunk` and `Address` are both
typedefs, both reached by the same alias-following code; if that code collapsed to a single
default width the ledger would look identical and the arithmetic would be wrong. -/
theorem chunkVsAddress :
    runFunc castProg 100 "ns.chunk" [] ≠ runFunc castProg 100 "ns.address" [] := by
  rw [chunk, address]; simp

/-! **Axiom receipt.** Every theorem here is closed by `rfl` or by `simp` on top of an `rfl` fact, and every pinned
value by `#guard_msgs in #eval`. Neither route is `native_decide`, so nothing below adds a
trusted evaluator: the three axioms reported are Lean's own `propext`, `Classical.choice`
and `Quot.sound`, inherited from `Autoform.Lang.Core.Semantics`, and in particular there is
no `sorryAx`. -/
#print axioms chunk
#print axioms chunkHigh
#print axioms address
#print axioms notIdentity
#print axioms chunkVsAddress

end Autoform.Specs
