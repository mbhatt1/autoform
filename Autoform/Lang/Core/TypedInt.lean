import Autoform.Lang.Core.Syntax
import Autoform.Lang.Core.Numeric

/-!
# Core — width-typed integer operators

`Dialect.cLike` performs every *untyped* integer operation at 32 bits
(`Dialect.toNumConfig .cLike = NumConfig.c32Wrapv`). That is right for C `int` and Java
`int` and silently wrong for everything wider or unsigned: `100000L * 100000L` was
`1410065408` (Java: `10000000000`), SQLite's `(i64)0x1a640 << 32` was a shift-count hole,
and `vdbeSorterTreeDepth`'s `i64` loop wrapped at `2^32` and ran out of fuel
(`docs/scale.md`, STRATEGY §28 item 5).

A `Val.int` carries no type, so the width cannot be recovered at run time. The exporter
knows it statically (it already resolves C types for casts, `sizeof` and the signedness
of `>>`), so it **names the type in the operator**: `"*:i64"` is C multiplication of two
`long`s, `">>:u32"` a right shift of an `unsigned int`, `"<:u64"` a comparison after the
usual arithmetic conversions to `unsigned long`, `"+:j64"` Java `long` addition. The
same device `cast:i64` already uses: a typed operator is still `Expr.binop`/`Expr.unop`,
so hole-freedom, fuel monotonicity, rendering and the ledger need no new case.

## What a typed operator computes

`op:T` with operands `a`, `b`:

1. **Conversion.** Each integer operand is converted to `T` (`IntType.wrap`): the usual
   arithmetic conversions of C11 6.3.1.8 / JLS 5.6.2, which are value-preserving or
   modular, and *only* those two. This is exact provided each operand holds the
   mathematical value of its own C/Java object — which every value Core produces does
   (literals, typed results, `cast:*`). A `bool` operand is `0`/`1` first (C's
   comparison results; `Dialect.promotesBool`). For a shift only the LEFT operand is
   converted; the count keeps its own value (C11 6.5.7p3, JLS 15.19).
2. **The operation at `T`**, through `NumConfig` — the same functions the untyped path
   uses, at a different width.
3. **Policy.** C: unsigned arithmetic wraps (defined); signed overflow follows the ONE
   configured C policy, `Dialect.toNumConfig .cLike`'s `onSignedOverflow` (`wrap`, i.e.
   `-fwrapv`, so the `cc` oracle agrees; flip it there to `undefined` and every width
   holes on overflow instead). Things C leaves undefined at every policy are holes:
   division or remainder by zero, `MIN / -1` and `MIN % -1`, a shift count outside
   `[0, width)`. Java: `NumConfig.java32`/`java64` — wraps, shift counts masked, `MIN /
   -1 = MIN`, division by zero throws `ArithmeticException`.

Anything else is a hole: an operand that is not an integer (or C `bool`), an unknown
type tag, an unknown operator. The exporter emits a typed operator only when it resolved
the type; when it cannot, it emits a hole rather than the untyped (32-bit) operator.
-/

namespace Autoform.Core

/-- Whose conversion, overflow and shift rules a typed operator follows. -/
inductive IntLang where
  | c
  | java
  deriving Repr, Inhabited, DecidableEq

/-- The static type a typed operator is performed at. -/
structure IntTag where
  lang : IntLang
  type : IntType
  deriving Repr, Inhabited, DecidableEq

namespace IntTag

/-- The type tags the exporter emits. Arithmetic in C and Java is never performed below
`int` (the integer promotions / binary numeric promotion widen first), so 32 and 64 are
the only widths. -/
def ofString : String → Option IntTag
  | "i32" => some ⟨.c, .signed .w32⟩
  | "i64" => some ⟨.c, .signed .w64⟩
  | "u32" => some ⟨.c, .unsigned .w32⟩
  | "u64" => some ⟨.c, .unsigned .w64⟩
  | "j32" => some ⟨.java, .signed .w32⟩
  | "j64" => some ⟨.java, .signed .w64⟩
  | _     => none

/-- The arithmetic configuration of this tag. C takes its policies from
`Dialect.toNumConfig .cLike` — the single place the C overflow policy is configured
(STRATEGY §16) — and only its width/signedness from the tag. -/
def config (t : IntTag) : NumConfig :=
  match t.lang with
  | .c    => { Dialect.cLike.toNumConfig with type := t.type }
  | .java => { NumConfig.java32 with type := t.type }

end IntTag

/-- Split `"<op>:<tag>"` (a three-character tag) into the base operator and its tag.
Written over `List Char` so that it reduces by `rfl`/`decide`/`simp` on literal
operators: proofs about untyped operators (`"+"`, `"cast:u8"`) see `none` directly. -/
def splitTypedOp (op : String) : Option (String × IntTag) :=
  match op.toList.reverse with
  | c2 :: c1 :: c0 :: ':' :: rest =>
      (IntTag.ofString (String.ofList [c0, c1, c2])).map (String.ofList rest.reverse, ·)
  | _ => none

/-- An operand of a typed integer operator: an integer, or a C `bool` as `0`/`1`. -/
def typedOperand : Val → Option Int
  | .int x  => some x
  | .bool b => some (if b then 1 else 0)
  | _       => none

/-- A `NumResult` as an evaluation result, under the tag's language. C division by zero
is undefined (C11 6.5.5p5), so it is a hole, not an exception; Java throws. -/
def typedNumToE (t : IntTag) : NumResult → EResult
  | .ok v    => .val (.int v)
  | .divZero =>
      match t.lang with
      | .c    => .hole "ub:division by zero"
      | .java => .exn (.str "ArithmeticException")
  | .trap r  => .exn (.str r)
  | .ub r    => .hole s!"ub:{r}"

/-- `/` and `%` at a typed width. C makes `MIN / -1` (and therefore `MIN % -1`) undefined
whatever the overflow policy — `-fwrapv` does not define it and x86 traps — so the C arm
holes on an unrepresentable quotient before `NumConfig` can wrap it. -/
def typedDivMod (t : IntTag) (isDiv : Bool) (x y : Int) : EResult :=
  let nc := t.config
  if y == 0 then typedNumToE t .divZero
  else if t.lang == .c && !nc.type.inRange (nc.quot x y) then
    .hole "ub:signed division overflow (MIN / -1)"
  else typedNumToE t (if isDiv then nc.div x y else nc.mod x y)

/-- The typed binary operators. `none` when `op` carries no type tag, so the caller's
untyped behaviour is untouched. -/
def typedIntBinop (op : String) (a b : Val) : Option EResult :=
  (splitTypedOp op).map fun (base, t) =>
    let nc := t.config
    match typedOperand a, typedOperand b with
    | some x0, some y0 =>
      let x := nc.type.wrap x0
      let y := nc.type.wrap y0
      match base with
      | "+"   => typedNumToE t (nc.add x y)
      | "-"   => typedNumToE t (nc.sub x y)
      | "*"   => typedNumToE t (nc.mul x y)
      | "/"   => typedDivMod t true x y
      | "%"   => typedDivMod t false x y
      | "&"   => typedNumToE t (nc.band x y)
      | "|"   => typedNumToE t (nc.bor x y)
      | "^"   => typedNumToE t (nc.bxor x y)
      -- Shifts: the count `y0` is NOT converted to the left operand's type.
      | "<<"  => typedNumToE t (nc.shl x y0)
      | ">>"  => typedNumToE t (nc.shr x y0)
      | ">>>" => typedNumToE t ({ nc with negRightShift := .logical }.shr x y0)
      | "<"   => .val (.bool (x < y))
      | "<="  => .val (.bool (x ≤ y))
      | ">"   => .val (.bool (x > y))
      | ">="  => .val (.bool (x ≥ y))
      | "=="  => .val (.bool (x == y))
      | "!="  => .val (.bool (!(x == y)))
      | _     => .hole s!"binop:{op}"
    | _, _ => .hole s!"binop:{op}"

/-- The typed unary operators: `-` and `~` at a width. -/
def typedIntUnop (op : String) (a : Val) : Option EResult :=
  (splitTypedOp op).map fun (base, t) =>
    let nc := t.config
    match typedOperand a with
    | some x0 =>
      let x := nc.type.wrap x0
      match base with
      | "-" => typedNumToE t (nc.neg x)
      | "~" => typedNumToE t (nc.bnot x)
      | _   => .hole s!"unop:{op}"
    | none => .hole s!"unop:{op}"

/-! ## Pinned behaviour

Each line is a measured or specified value; `#guard` fails the build on a regression. -/

private def intOf : Option EResult → Option Int
  | some (.val (.int v)) => some v
  | _ => none
private def boolOf : Option EResult → Option Bool
  | some (.val (.bool v)) => some v
  | _ => none
private def holeOf : Option EResult → Option String
  | some (.hole l) => some l
  | _ => none

-- An untyped operator is not claimed.
#guard (typedIntBinop "+" (.int 1) (.int 2)).isNone
#guard (typedIntUnop "cast:u8" (.int 1)).isNone
#guard (typedIntBinop "+:i16" (.int 1) (.int 2)).isNone
-- STRATEGY §28 item 5: Java `100000L*100000L` is 10^10; the untyped (32-bit) answer was
-- 1410065408, which is what `int` still gives.
#guard intOf (typedIntBinop "*:j64" (.int 100000) (.int 100000)) == some 10000000000
#guard intOf (typedIntBinop "*:j32" (.int 100000) (.int 100000)) == some 1410065408
-- C `long` under LP64, and the wrap at 64 bits (cc -fwrapv agrees).
#guard intOf (typedIntBinop "*:i64" (.int 100000) (.int 100000)) == some 10000000000
#guard intOf (typedIntBinop "+:i64" (.int 9223372036854775807) (.int 1))
        == some (-9223372036854775808)
-- `validJulianDay`: `((i64)0x1a640 << 32) | 0x1072fdff` is 464269060799999.
#guard intOf (typedIntBinop "|:i64" (.int (0x1a640 * 2 ^ 32)) (.int 0x1072fdff))
        == some 464269060799999
#guard intOf (typedIntBinop "<<:i64" (.int 0x1a640) (.int 32)) == some (0x1a640 * 2 ^ 32)
#guard holeOf (typedIntBinop "<<:i32" (.int 0x1a640) (.int 32))
        == some "ub:shift count out of range"
-- Unsigned: modular, and the usual arithmetic conversions of a negative operand.
#guard intOf (typedIntBinop "-:u32" (.int 0) (.int 1)) == some 4294967295
#guard intOf (typedIntBinop "*:u64" (.int 18446744073709551615) (.int 2))
        == some 18446744073709551614
#guard boolOf (typedIntBinop "<:u32" (.int (-1)) (.int 1)) == some false
#guard boolOf (typedIntBinop "<:i64" (.int (-1)) (.int 1)) == some true
#guard intOf (typedIntBinop "/:u32" (.int (-1)) (.int 2)) == some 2147483647
#guard intOf (typedIntBinop ">>:u32" (.int (-8)) (.int 1)) == some 2147483644
#guard intOf (typedIntBinop ">>:i32" (.int (-8)) (.int 1)) == some (-4)
#guard intOf (typedIntUnop "-:u32" (.int 1)) == some 4294967295
#guard intOf (typedIntUnop "~:u64" (.int 0)) == some 18446744073709551615
-- C leaves these undefined at every overflow policy.
#guard holeOf (typedIntBinop "/:i32" (.int 1) (.int 0)) == some "ub:division by zero"
#guard holeOf (typedIntBinop "/:i64" (.int (-9223372036854775808)) (.int (-1)))
        == some "ub:signed division overflow (MIN / -1)"
-- Java defines them.
#guard intOf (typedIntBinop "/:j32" (.int (-2147483648)) (.int (-1))) == some (-2147483648)
#guard intOf (typedIntBinop "%:j32" (.int (-2147483648)) (.int (-1))) == some 0
#guard intOf (typedIntBinop "<<:j32" (.int 1) (.int 33)) == some 2
#guard intOf (typedIntBinop "<<:j64" (.int 1) (.int 65)) == some 2
#guard intOf (typedIntBinop ">>>:j32" (.int (-1)) (.int 28)) == some 15
#guard intOf (typedIntBinop ">>>:j64" (.int (-1)) (.int 60)) == some 15
-- A C `bool` (comparison result) is 0/1; a string is not an integer.
#guard intOf (typedIntBinop "+:i64" (.bool true) (.int 1)) == some 2
#guard holeOf (typedIntBinop "+:i64" (.str "x") (.int 1)) == some "binop:+:i64"

/-! ## Lemmas

The typed operators are the untyped ones at another width, and they agree with plain
`Int` arithmetic exactly when the result is representable. -/

theorem splitTypedOp_plus : splitTypedOp "+" = none := rfl

/-- C `long` addition is mathematical addition whenever the operands and the sum are
representable in 64 bits. -/
theorem typedIntBinop_add_i64 {x y : Int}
    (hx : IntType.inRange (.signed .w64) x = true) (hy : IntType.inRange (.signed .w64) y = true)
    (h : IntType.inRange (.signed .w64) (x + y) = true) :
    typedIntBinop "+:i64" (.int x) (.int y) = some (.val (.int (x + y))) := by
  have hx' := IntType.wrap_of_inRange hx
  have hy' := IntType.wrap_of_inRange hy
  simp [typedIntBinop, splitTypedOp, IntTag.ofString, IntTag.config, typedOperand,
    Dialect.toNumConfig, NumConfig.c32Wrapv, NumConfig.c32, NumConfig.add, NumConfig.finish,
    typedNumToE, hx', hy', h]

/-- Every `ok` result of a typed arithmetic operator is representable at its width:
`finish` lands in range (`NumConfig.finish_inRange`). -/
theorem typed_add_inRange (t : IntTag) (x y v : Int) (h : t.config.add x y = .ok v) :
    t.config.type.inRange v = true :=
  NumConfig.finish_inRange _ _ _ h

end Autoform.Core
