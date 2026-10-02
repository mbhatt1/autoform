import Autoform.Lang.Core.Syntax
import Autoform.Lang.Core.Numeric
import Autoform.Lang.Core.TypedInt
import Autoform.Lang.Core.Stdlib
import Autoform.Lang.Core.Address
import Autoform.Lang.Core.Boxed

/-!
# Core — semantics

A fuel-indexed definitional interpreter for the universal core language. This is the
formal interpreter that an arbitrary codebase is mapped onto.

Design commitments, each of which exists to keep the trust story honest:

* **Total.** Structurally recursive on fuel, so evaluation always terminates and Lean
  accepts it without `partial`. No `sorry`, no `unsafe`.
* **Holes are observable.** Reaching a hole yields a distinguished outcome — not an
  error, not a value. A theorem about a program can therefore never accidentally
  quantify over behaviour we failed to translate.
* **Ignorance is distinguishable from behaviour.** `outOfFuel` (we did not run long
  enough), `hole` (we did not translate this), a raised exception, and a genuine result
  are four different outcomes, because they mean four different things.
* **The heap is explicit.** Objects are boxed and mutable; the heap is threaded through
  evaluation rather than hidden in a monad, so the recursion stays visibly structural.
-/

namespace Autoform.Core

/-- Variable environment. -/
abbrev Env := List (String × Val)

namespace Env

/-- Look up a variable; unbound reads are `unit`. -/
def get (ρ : Env) (x : String) : Val :=
  match ρ.find? (·.1 == x) with
  | some (_, v) => v
  | none        => .unit

/-- Bind a variable, shadowing any previous binding. -/
def set (ρ : Env) (x : String) (v : Val) : Env := (x, v) :: ρ

/-- Remove every binding of a variable (`del x`). -/
def del (ρ : Env) (x : String) : Env := ρ.filter (·.1 != x)

end Env




/-!
## Dialect-sensitive arithmetic

Integer division and modulo are **not** universal: Python floors, C and Java truncate
toward zero. Hardcoding one convention silently mistranslates every other language, so
the dialect is carried explicitly and recorded by the transpiler.

This was not designed in. It was found by `scripts/differential.py`, which caught
`fmod(6, -9)` returning `6` in Lean against CPython's `-3`, and the same error
propagating into `gcdish`. That is what the conformance oracle is for.
-/

/-- Integer division under a dialect.

Unused by `applyBinop` (superseded by `NumConfig.quot`, per this section's own intro);
kept, and kept exhaustive, because `Numeric.lean` cites it as the pattern's first
instance. JavaScript has no integer division at all (`7 / 2` is `3.5`; `applyBinop`
routes `.javascript` through `jsIntDiv`), so its arm is the truncating quotient that
matches its truncating remainder below -- NOT `.python`'s floor, which was this arm's
earlier, wrong answer. -/
def Dialect.idiv : Dialect → Int → Int → Int
  | .python,     a, b => Int.fdiv a b
  | .cLike,      a, b => Int.tdiv a b
  | .javascript, a, b => Int.tdiv a b

/-- Integer remainder under a dialect. See `idiv` — unused, kept exhaustive and
consistent with it. JS `%` truncates (`-7 % 3` is `-1`), like C. -/
def Dialect.imod : Dialect → Int → Int → Int
  | .python,     a, b => Int.fmod a b
  | .cLike,      a, b => Int.tmod a b
  | .javascript, a, b => Int.tmod a b


/-- Result of executing a statement: how control left it. -/
inductive Ctl where
  | normal    : Env → Ctl
  | ret       : Val → Ctl
  | brk       : Env → Ctl
  | cont      : Env → Ctl
  | exn       : Val → Ctl
  | hole      : String → Ctl
  | outOfFuel : Ctl
  deriving Repr, Inhabited

/-- Lift a machine-integer outcome into an evaluation outcome.

`ub` becomes a **hole**, not a number. A program that relies on undefined behaviour has
no defined meaning at that point, so the honest translation is "we cannot say" — the same
discipline applied to untranslated constructs. Returning some plausible number here would
be the same class of error as the original modulo bug, only harder to detect. -/
def numToE : NumResult → EResult
  | .ok v      => .val (.int v)
  | .divZero   => .exn (.str "ZeroDivisionError")
  | .trap r    => .exn (.str r)
  | .ub r      => .hole s!"ub:{r}"

/-! ### Floating point

`Autoform/Lang/Core/Float.lean` supplies the value domain and the arithmetic; this section
is only the wiring. Three decisions are recorded here because they are the ones that can
be silently wrong.

**Promotion.** In mixed `int`/`float` *arithmetic* both Python and C convert the integer
to a double and compute in binary64, so `flOfVal` promotes. Python raises `OverflowError`
if the integer is too large to convert (reachable only under `.python`, since `.cLike`
integers are 32-bit and always convertible), and `FConfig.ofInt` reproduces that.

**Comparison does *not* promote — under Python.** CPython compares an `int` and a `float`
*exactly*: `10**23 == 1e23` is `False`, because `1e23` is really
`99999999999999991611392`. C has no bignums and its `==` promotes, so the two dialects
genuinely differ here and `flCmp` splits on the dialect. Promoting under `.python` would
be a silent wrong answer of the `floorDiv` family.

**`/` on two integers is still floor division, and that is now a known wrong answer for
Python.** CPython's `/` is *true* division (`7 / 2 == 3.5`) and `//` floors. The
transpiler currently maps Python's `//` onto the `"/"` operator string (see the note above
`applyBinop_py_div` and `Refine.lean`'s discussion of `op:floorDiv`), so `"/"` on two
`.int`s is left exactly as it was — changing it would silently break every `//` in the
corpora. `"//"` is now a distinct operator with the floor semantics, so the fix is in
`cartographer/render_lean.py`: emit `"//"` for floor division and `"/"` for true division,
after which `"/"` on two `.int`s under `.python` must become `flBinop`. Until then this is
a recorded silent mistranslation, not an accident.

**NaN is unordered.** `flCmp` returns `none`, and `ordToE` turns that into `false` for
`<`, `<=`, `>`, `>=` and `==`, and `true` for `!=`. That is CPython's behaviour and it is
not expressible by an `Ordering` alone. -/

/-- Lift a float outcome into an evaluation outcome. `ub` and `unmodelled` both become
holes — the first because the language does not define the result, the second because we
have not modelled it — and they keep distinct labels so the ledger can tell them apart. -/
def fresToE : FResult → EResult
  | .ok v         => .val (.float v)
  | .exn r        => .exn (.str r)
  | .ub r         => .hole s!"ub:{r}"
  | .unmodelled r => .hole r

/-- Promote a numeric value to the dialect's float format, as mixed arithmetic requires.
`none` means "not a number", not "failed". -/
def flOfVal (d : Dialect) : Val → Option FResult
  | .float f => some (if f.fmt == (d.toFConfig).fmt then .ok f
                      else .unmodelled "float:format-mismatch")
  | .int n   => some ((d.toFConfig).ofInt n)
  | _        => none

/-- Compare two numeric values, at least one a float. `none` is *unordered* (NaN, or a
non-numeric operand), which is not the same as "equal" or "less". -/
def flCmp (d : Dialect) : Val → Val → Option Ordering
  | .float x, .float y => Fl.cmpv x y
  | .int n,   .float y =>
      match d with
      | .python => Fl.cmpIntv n y                     -- exact, no conversion
      -- `comparesIntFloatExactly d = false` for both: JS has no separate int type to be
      -- exact about, so it promotes like C.
      | .cLike | .javascript =>
          match (d.toFConfig).ofInt n with
          | .ok x => Fl.cmpv x y
          | _     => none
  | .float x, .int n   =>
      (match d with
       | .python => Fl.cmpIntv n x
       | .cLike | .javascript =>
           match (d.toFConfig).ofInt n with
           | .ok y => Fl.cmpv y x
           | _     => none).map Ordering.swap
  | _,        _        => none

/-- Turn a comparison outcome into the answer for a relational operator. Unordered is
`false` everywhere except `!=`. -/
def ordToE (op : String) (o : Option Ordering) : EResult :=
  match op with
  | "<"  => .val (.bool (o == some .lt))
  | "<=" => .val (.bool (o == some .lt || o == some .eq))
  | ">"  => .val (.bool (o == some .gt))
  | ">=" => .val (.bool (o == some .gt || o == some .eq))
  | "==" => .val (.bool (o == some .eq))
  | "!=" => .val (.bool (!(o == some .eq)))
  | _    => .hole s!"binop:{op}"

/-- Binary operators where at least one operand is a float. -/
def flBinop (d : Dialect) (op : String) (a b : Val) : EResult :=
  match op with
  -- Reached only when the left operand did not decide the result (`evalExpr`
  -- short-circuits first), exactly as for `applyBinop`'s own `&&`/`||` arms, so under
  -- value semantics the answer is the right operand: Node's `0.0 || 2` is `2`, and
  -- CPython's `0.0 or 2` is `2`, not `True`.
  | "&&" => .val (if d.boolOpsAreValues then b else .bool (a.truthy && b.truthy))
  | "||" => .val (if d.boolOpsAreValues then b else .bool (a.truthy || b.truthy))
  | "<" | "<=" | ">" | ">=" | "==" | "!=" => ordToE op (flCmp d a b)
  | "+" | "-" | "*" | "/" | "%" =>
      match flOfVal d a, flOfVal d b with
      | some (.ok x), some (.ok y) =>
          let fc := d.toFConfig
          fresToE (match op with
                   | "+" => fc.add x y
                   | "-" => fc.sub x y
                   | "*" => fc.mul x y
                   | "/" => fc.div x y
                   -- JS `%` on a `Number` is the remainder of TRUNCATED division
                   -- (sign of the dividend): Node's `-7.5 % 2` is `-1.5`, CPython's
                   -- is `0.5`. That is C's `fmod`, which IEEE makes exact.
                   -- `.cLike` likewise: the only `.cLike` languages in which `%`
                   -- accepts a floating operand at all are Java and Kotlin (C, C++ and
                   -- Go reject it at compile time), and both define it as the
                   -- truncated remainder (JLS 15.17.3: `-5.5 % 2.0` is `-1.5`). It was
                   -- Python's floored `pyMod` here, which answered `0.5`.
                   | _   => match d with
                            | .javascript | .cLike => fc.fmod x y
                            | .python              => fc.pyMod x y)
        -- a failed promotion (Python's `OverflowError` on a huge int) is the answer
      | some r, some (.ok _) => fresToE r
      | some (.ok _), some r => fresToE r
      | some r, some _       => fresToE r
      | _, _                 => .hole s!"binop:{op}:non-numeric"
  -- CPython's `float.__floordiv__` is a multi-step rounding sequence (`fmod`, then a
  -- rounded subtraction, then `floor`, then a half-ulp correction). Modelling it
  -- approximately would produce divergences on the boundary cases it exists to get
  -- right, so it is a hole until it is modelled properly.
  | "//" => .hole "binop://:float-floordiv"
  -- `x ** y` on floats is `pow`, which IEEE does define, but which this model does not
  -- implement. See `Float.lean`'s "what is deliberately NOT modelled".
  | "**" => .hole "float:pow"
  | _    => .hole s!"binop:{op}"

/-- JavaScript `x / y` on two operands that Core holds as `.int`s.

A JS `Number` is a binary64, so the answer is IEEE division of the two doubles. When the
quotient is an exact integer it is returned as `.int` (`6 / 3` is `2`), keeping integer
code on the integer path; otherwise -- a fraction, division by zero (`Infinity`/`NaN`),
or `0 / -3` (`-0`, which `.int` cannot represent) -- it is computed by `flBinop` as
IEEE division under `Dialect.toFConfig .javascript` (`cDouble`, `onDivZero := .ieee`).
The usual `.javascript` caveat applies: past 2^53 the `.int` path is exact where Node
would round. -/
def jsIntDiv (x y : Int) : EResult :=
  if y != 0 && Int.tmod x y == 0 && !(x == 0 && y < 0) then .val (.int (Int.tdiv x y))
  else flBinop .javascript "/" (.int x) (.int y)

/-- JavaScript `x % y` on two `.int`s: the remainder of TRUNCATED division, taking the
sign of the dividend (`-7 % 3` is `-1`). `x % 0` is `NaN` and a zero remainder of a
negative dividend is `-0` (`-6 % 3`); neither is an `.int`, so both go to the float path
(`flBinop`, which uses `fmod` under `.javascript`). -/
def jsIntMod (x y : Int) : EResult :=
  if y != 0 && (Int.tmod x y != 0 || x >= 0) then .val (.int (Int.tmod x y))
  else flBinop .javascript "%" (.int x) (.int y)

/-! ### JavaScript bitwise operators: ToInt32 / ToUint32

Every JS bitwise operator converts its operands to 32-bit integers first (ECMA-262
`ToInt32`/`ToUint32`, i.e. reduction modulo 2^32), and every one but `>>>` yields a
signed 32-bit result; the shift count is `ToUint32(rhs) & 31`. `.javascript` borrows
`NumConfig.python` (unbounded) for `+`/`-`/`*`, so routing `&`/`|`/`^`/`<<`/`>>`/`~`
through it gave bignum answers: `1 << 32` was `4294967296` (Node: `1`), `1 << 31` was
`2147483648` (Node: `-2147483648`), `~2147483648` was `-2147483649` (Node:
`2147483647`), and `-1 >>> 0` was a `ub` hole (Node: `4294967295`).

**Precision guard.** A Core `.int` under `.javascript` is exact past 2^53 where Node's
double would already have rounded, so ToInt32 of such a value can disagree with Node.
Operands with `|n| > 2^53` are a hole rather than an answer. Float operands (`1.5 | 0`)
never reach here: `flBinop` holes every bitwise operator. -/

/-- ECMA-262 `ToUint32` on an integer: reduction into `[0, 2^32)`. -/
def jsToUint32 (n : Int) : Int := n % 4294967296

/-- ECMA-262 `ToInt32` on an integer: reduction into `[-2^31, 2^31)`. -/
def jsToInt32 (n : Int) : Int :=
  let m := jsToUint32 n
  if m ≥ 2147483648 then m - 4294967296 else m

/-- `|n| ≤ 2^53`: every such integer is an exact binary64, so ToInt32 of the Core value
is ToInt32 of the Node value. -/
def jsExactInt (n : Int) : Bool := n.natAbs ≤ 9007199254740992

/-- JS `x op y` for a bitwise operator on two `.int`s. -/
def jsBitwise (op : String) (x y : Int) : EResult :=
  if !(jsExactInt x && jsExactInt y) then .hole "js:bitwise:operand-beyond-2^53"
  else
    let ux := (jsToUint32 x).toNat
    let uy := (jsToUint32 y).toNat
    let s  := uy % 32
    match op with
    | "&"   => .val (.int (jsToInt32 (Nat.land ux uy)))
    | "|"   => .val (.int (jsToInt32 (Nat.lor ux uy)))
    | "^"   => .val (.int (jsToInt32 (Nat.xor ux uy)))
    | "<<"  => .val (.int (jsToInt32 (jsToInt32 x * 2 ^ s)))
    -- arithmetic (sign-propagating): floor division of the signed 32-bit value
    | ">>"  => .val (.int (Int.fdiv (jsToInt32 x) (2 ^ s)))
    -- zero-filling, and the result is UNSIGNED: `-1 >>> 0` is `4294967295`
    | ">>>" => .val (.int ((ux / 2 ^ s : Nat) : Int))
    | _     => .hole s!"binop:{op}"

/-- JS `~x` on an `.int`: `-ToInt32(x) - 1`, always in int32 range. -/
def jsBitNot (x : Int) : EResult :=
  if jsExactInt x then .val (.int (-(jsToInt32 x) - 1))
  else .hole "js:bitwise:operand-beyond-2^53"

/-! ### JavaScript `===` and `==`

`===` (IsStrictlyEqual) is `false` across JS types and value comparison within one,
except that objects compare by identity. `==` (IsLooselyEqual) agrees with it on two
operands of the same JS type; across types it coerces (`1 == "1"`, `0 == false`,
`[1] == 1` are all `true`) through ToNumber/ToPrimitive, which this model does **not**
implement -- those are holes. The one cross-type case that needs no coercion is decided:
`null`/`undefined` are loosely equal to each other and to nothing else.

Core's value representation limits what can be answered:

* `.int` and `.float` are both a JS Number, compared numerically (`1 === 1.0`), with IEEE
  rules via `flCmp` (`NaN !== NaN`, `0 === -0`).
* `.unit` is **both** `null` and `undefined` -- Core does not distinguish them -- so
  `.unit === .unit` is a hole (`null === undefined` is `false`), while `.unit == .unit` is
  `true` in every combination and `.unit == <non-nullish>` is `false`.
* Objects compare by identity. A `.ref` and a named `.fn` carry it; an unboxed
  `.list`/`.tuple`/`.dict` or a closure value does not, so two of those are a hole. -/

/-- The JS type of a Core value as far as equality needs it: 0 Number, 1 String,
2 Boolean, 3 null/undefined, 4 Object. `none` for values that are not JS values. -/
def jsEqTag : Val → Option Nat
  | .int _ | .float _ => some 0
  | .str _ => some 1
  | .bool _ => some 2
  | .unit => some 3
  | .ref _ | .list _ | .tuple _ | .dict _ | .fn _ | .clos _ _ | .clsClos _ _
  | .bobj _ _ => some 4
  | .iref _ _ => none

/-- Equality of two values of the same JS type (`jsEqTag x = jsEqTag y`), where Core can
decide it. `.unit`/`.unit` is left to the caller (it differs between `==` and `===`). -/
def jsSameTypeEq : Val → Val → Option Bool
  | .int a,  .int b  => some (a == b)
  | .str a,  .str b  => some (a == b)
  | .bool a, .bool b => some (a == b)
  | .ref a,  .ref b  => some (a == b)
  | .fn a,   .fn b   => some (a == b)
  | x, y =>
      if x.kind == 3 || y.kind == 3 then some (flCmp .javascript x y == some .eq)
      else none

/-- JS `x === y` (`strict := true`) or `x == y` (`strict := false`), negated if `neg`. -/
def jsEqE (strict neg : Bool) (x y : Val) : EResult :=
  let r : Except String Bool :=
    match jsEqTag x, jsEqTag y with
    | some tx, some ty =>
        if tx == ty then
          if tx == 3 then
            if strict then .error "js:===:null-vs-undefined" else .ok true
          else match jsSameTypeEq x y with
               | some b => .ok b
               | none   => .error "js:eq:object-identity-unknown"
        else if strict || tx == 3 || ty == 3 then .ok false
        else .error "js:==:cross-type-coercion"
    | _, _ => .error "js:eq:non-js-value"
  match r with
  | .ok b    => .val (.bool (if neg then !b else b))
  | .error l => .hole l

/-- Whether `==`/`!=` on these operands has to consult the heap.

Only a REFERENCE forces it: two distinct objects with equal contents are `==` in Python, and
no structural compare of two refs can see that. Everything else stays on `applyBinop`, which
is heap-free and reducible -- the property `Refine.lean` is built on. Named rather than
inlined so proofs can discharge it by `simp` on concrete operands. -/
def binopNeedsHeap (op : String) (x y : Val) : Bool :=
  (op == "==" || op == "!=") &&
    -- A reference, or a VALUE container (list 5, tuple 6, dict 7, builtin-based 12) that may
    -- hold one: `(xs,) == ([1],)` compares a boxed list at depth 1, and `Val.beq` would
    -- compare it by address.
    (x.kind == 5 || x.kind == 6 || x.kind == 7 || x.kind == 8 || x.kind == 12 ||
     y.kind == 5 || y.kind == 6 || y.kind == 7 || y.kind == 8 || y.kind == 12)

@[simp] theorem binopNeedsHeap_int_left (op : String) (i : Int) (y : Val) :
    binopNeedsHeap op (.int i) y = ((op == "==" || op == "!=") &&
      (y.kind == 5 || y.kind == 6 || y.kind == 7 || y.kind == 8 || y.kind == 12)) := by
  simp [binopNeedsHeap, Val.kind]

@[simp] theorem binopNeedsHeap_arith (x y : Val) (op : String)
    (h : op ≠ "==") (h2 : op ≠ "!=") : binopNeedsHeap op x y = false := by
  simp [binopNeedsHeap, beq_iff_eq, h, h2]

/-! ### `bool` in integer contexts under `.cLike`

C has no boolean results: `a < b`, `a == b`, `!a`, `a && b` are `int` 0 or 1 (C11
6.5.8p6, 6.5.9p3, 6.5.3.3p5, 6.5.13p3, 6.5.14p3), and a `_Bool` promotes to `int`
(6.3.1.1p2). C++ does have `bool`, and integral promotion turns it into `int` 0/1 in
arithmetic, comparison and bitwise contexts ([conv.prom]/6). Java, Go and Kotlin share
`.cLike` too, and there `a < b` is a `boolean` and mixing it with an integer is a
**compile error** — so no well-typed program of theirs ever reaches the cases below.

Core keeps producing `Val.bool` for comparisons under `.cLike` (Java's `boolean` and
C++'s `bool` need it, and `Refine.applyBinop_int_lt` & co. state it for every dialect),
and instead PROMOTES a `bool` operand to `0`/`1` wherever it meets an integer or a float:
the C++ rule, which under C is the same arithmetic with the 0/1 already applied. Before
this, `int t = (a < b); if (t == 1) ...` compared `Val.bool true` with `Val.int 1` via
`Val.beq` and answered **false** (cc: true) — a silent wrong answer measured on SQLite
(`docs/scale.md`), and `(a<b) + (b<a)` was a hole.

Two `bool`s under `&`, `|`, `^` stay a `bool` (Java's logical `&`; in C the 0/1 that a
later integer context promotes), and two `bool`s under `==`/`!=`/`&&`/`||` take the
existing path, whose truth value is the same either way. Every other operator on two
`bool`s promotes both (C/C++ only; a compile error elsewhere).

What is NOT done here: the RETURN conversion. `int f(void) { return a < b; }` returns
`Val.bool`, which every integer context above reads as `0`/`1`; the C oracle
(`scripts/differential.py`) compares a `bool` result against an integer-typed C result as
`0`/`1` for the same reason. -/

/-- Does this dialect promote `bool` to `0`/`1` in integer contexts? See above. -/
def Dialect.promotesBool : Dialect → Bool
  | .python     => false
  | .cLike      => true
  | .javascript => false

/-- `false`/`true` as the integers C gives them. -/
def boolToInt (b : Bool) : Int := if b then 1 else 0

/-- The operators a promoted `bool` takes part in as an integer. -/
def cIntOps : List String :=
  ["+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", ">>>", "<", "<=", ">", ">=", "==", "!="]

/-- `applyBinop .cLike op (.int x) (.int y)` for `op ∈ cIntOps`, restated so the promoted
`bool` arms of `applyBinop` can use it without recursion. `cIntBinop_eq` (below
`applyBinop`) proves the two agree, so they cannot drift apart. -/
def cIntBinop (op : String) (x y : Int) : EResult :=
  let nc := Dialect.cLike.toNumConfig
  match op with
  | "+"   => numToE (nc.add x y)
  | "-"   => numToE (nc.sub x y)
  | "*"   => numToE (nc.mul x y)
  | "/"   => numToE (nc.div x y)
  | "%"   => numToE (nc.mod x y)
  | "&"   => numToE (nc.band x y)
  | "|"   => numToE (nc.bor x y)
  | "^"   => numToE (nc.bxor x y)
  | "<<"  => numToE (nc.shl x y)
  | ">>"  => numToE (nc.shr x y)
  | ">>>" => numToE ({ nc with negRightShift := .logical }.shr x y)
  | "<"   => .val (.bool (x < y))
  | "<="  => .val (.bool (x ≤ y))
  | ">"   => .val (.bool (x > y))
  | ">="  => .val (.bool (x ≥ y))
  | "=="  => .val (.bool (x == y))
  | "!="  => .val (.bool (!(x == y)))
  | _     => .hole s!"binop:{op}"

/-- What `applyBinop` answers for operands no typed arm claims: the generic tail of its
match (structural `==`/`!=`, value-or-bool `&&`/`||`, otherwise a hole). -/
def binopTail (d : Dialect) (op : String) (a b : Val) : EResult :=
  match op with
  | "==" => .val (.bool (Val.beq a b))
  | "!=" => .val (.bool (!Val.beq a b))
  | "&&" => .val (if d.boolOpsAreValues then b else .bool b.truthy)
  | "||" => .val (if d.boolOpsAreValues then b else .bool b.truthy)
  -- A width-typed operator (`"*:i64"`, `"<:u32"`, `"+:j64"`; `TypedInt.lean`) is
  -- claimed here: none of the literal arms above can match it. Untyped operators are
  -- `none` there, and keep their hole.
  | _    => match typedIntBinop op a b with
            | some r => r
            | none   => .hole s!"binop:{op}"

/-- The tail of `applyBinop`: operand pairs no typed arm there claims. A `bool` meeting a
number is promoted to 0/1 under `.cLike` (see `Dialect.promotesBool`); everything else is
`binopTail`. A separate function, not more arms of `applyBinop`'s match, because every
extra arm there multiplies the string-literal tests `simp` has to discharge in the
operator lemmas below. -/
def binopFallback (d : Dialect) (op : String) (a b : Val) : EResult :=
  match a, b with
  | .bool p, .int y =>
      if d.promotesBool && cIntOps.contains op then cIntBinop op (boolToInt p) y
      else binopTail d op a b
  | .int x, .bool q =>
      if d.promotesBool && cIntOps.contains op then cIntBinop op x (boolToInt q)
      else binopTail d op a b
  | .bool p, .float _ =>
      if d.promotesBool then flBinop d op (.int (boolToInt p)) b else binopTail d op a b
  | .float _, .bool q =>
      if d.promotesBool then flBinop d op a (.int (boolToInt q)) else binopTail d op a b
  | .bool p, .bool q =>
      if d.promotesBool then
        match op with
        | "&" => .val (.bool (p && q))
        | "|" => .val (.bool (p || q))
        | "^" => .val (.bool (p != q))
        | "==" | "!=" | "&&" | "||" => binopTail d op a b
        | _ => if cIntOps.contains op then cIntBinop op (boolToInt p) (boolToInt q)
               else binopTail d op a b
      else binopTail d op a b
  | _, _ => binopTail d op a b

/-- Built-in binary operators. Unknown operators are holes, not guesses.

Integer arithmetic goes through `NumConfig`, so width and overflow policy follow the
source dialect: Python gets bignums, C-like gets 32-bit two's-complement for an UNTYPED
operator. A width-typed operator (`"*:i64"`, `TypedInt.lean`) matches none of the literal arms
below and is answered by `binopTail`. -/
def applyBinop (d : Dialect) (op : String) (a b : Val) : EResult :=
  let nc := d.toNumConfig
  match op, a, b with
  -- JavaScript strict equality. Its own operator string, emitted by the exporter only for
  -- a JS `===`/`!==` source token (jssrc2cpg spells both `<operator>.equals`), and first
  -- in the match so the float arms below cannot claim it. See `jsEqE`.
  | "===", x, y =>
      match d with
      | .javascript => jsEqE true false x y
      | _           => .hole "binop:===:non-javascript"
  | "!==", x, y =>
      match d with
      | .javascript => jsEqE true true x y
      | _           => .hole "binop:!==:non-javascript"
  | "+",  .int x,   .int y   => numToE (nc.add x y)
  -- Item 6: a C `char*` is not a Python `str`. In C, `+` on pointers is POINTER
  -- ARITHMETIC and `<`/`>`/`==` compare ADDRESSES, not contents. Core has one `Val.str`
  -- for both, so applying Python's string semantics under `.cLike` would be a silent
  -- wrong answer of exactly the kind §12 is about. Under `.cLike` these are holes.
  | "+",  .str _,   .str _   =>
      if d.stringsAreValues then
        .val (.str (match a, b with | .str x, .str y => x ++ y | _, _ => ""))
      else .hole "str:pointer-arithmetic-not-modelled"
  | "+",  .list x,  .list y  => .val (.list (x ++ y))
  | "+",  .tuple x, .tuple y => .val (.tuple (x ++ y))
  | "-",  .int x, .int y => numToE (nc.sub x y)
  | "*",  .int x, .int y => numToE (nc.mul x y)
  -- JavaScript has no integer division. `NumConfig.python` (which `.javascript`
  -- borrows for its unbounded `+`/`-`/`*`) FLOORS, and answering with it reproduced the
  -- measured `.tsx`-as-Python bug (`docs/languages.md` §2) under a new name: `-7 % 3`
  -- gave `2` (Node: `-1`), `7 / 2` gave `3` (Node: `3.5`), `5 / 0` raised
  -- `ZeroDivisionError` (Node: `Infinity`). So `.javascript` splits off here; see
  -- `jsIntDiv`/`jsIntMod`.
  | "/",  .int x, .int y =>
      match d with
      | .javascript => jsIntDiv x y
      | _           => numToE (nc.div x y)
  | "%",  .int x, .int y =>
      match d with
      | .javascript => jsIntMod x y
      | _           => numToE (nc.mod x y)
  -- ### Bitwise operators
  --
  -- These are `&`, `|`, `^`, `<<`, `>>` and `>>>` — the **bitwise** operations, not the
  -- logical ones. `<operator>.and` / `<operator>.or` in a CPG are these, and the exporter
  -- used to map them onto `"&&"` / `"||"`, which returned a boolean where C returns a
  -- number: `(flags & MASK) == MASK` became `true == MASK`. That silent wrong answer is
  -- why they were unmapped for so long, and it is why they get their **own** operator
  -- strings here rather than sharing the logical ones.
  --
  -- The arithmetic is `NumConfig`'s, so the width and overflow policy are the dialect's:
  -- under `.cLike` an UNTYPED operator is 32-bit two's-complement, so `1 << 31` is `INT_MIN`
  -- (the wrapping config the oracle measures) and `-1 & 255` is `255`.
  --
  -- `>>` and `>>>` are **two different operators** and the difference is only visible on
  -- a negative left operand: C's `>>` on a signed value is arithmetic (sign-extending) and
  -- on an unsigned value it is logical (zero-filling). Core cannot recover the operand's
  -- signedness at run time — a `Val.int` carries no type — so the *exporter* decides,
  -- from the CPG's static type, which of the two it emits, and holes when the type is
  -- unknown. Collapsing them here would reintroduce exactly the `<operator>.and` mistake
  -- in a place where it is much harder to see.
  --
  -- JavaScript is the exception to "the arithmetic is `NumConfig`'s": its integers are
  -- unbounded for `+`, but its bitwise operators work on ToInt32/ToUint32 of their
  -- operands. See `jsBitwise`.
  | "&",  .int x, .int y =>
      match d with | .javascript => jsBitwise "&" x y  | _ => numToE (nc.band x y)
  | "|",  .int x, .int y =>
      match d with | .javascript => jsBitwise "|" x y  | _ => numToE (nc.bor x y)
  | "^",  .int x, .int y =>
      match d with | .javascript => jsBitwise "^" x y  | _ => numToE (nc.bxor x y)
  | "<<", .int x, .int y =>
      match d with | .javascript => jsBitwise "<<" x y | _ => numToE (nc.shl x y)
  | ">>", .int x, .int y =>
      match d with | .javascript => jsBitwise ">>" x y | _ => numToE (nc.shr x y)
  | ">>>", .int x, .int y =>
      match d with
      | .javascript => jsBitwise ">>>" x y
      | _           => numToE ({ nc with negRightShift := .logical }.shr x y)
  | "<",  .int x, .int y => .val (.bool (x < y))
  | "<=", .int x, .int y => .val (.bool (x ≤ y))
  | ">",  .int x, .int y => .val (.bool (x > y))
  | ">=", .int x, .int y => .val (.bool (x ≥ y))
  | "<",  .str x, .str y =>
      if d.stringsAreValues then .val (.bool (x < y))
      else .hole "str:pointer-compare-not-modelled"
  | ">",  .str x, .str y =>
      if d.stringsAreValues then .val (.bool (x > y))
      else .hole "str:pointer-compare-not-modelled"
  -- `int == int` is the same in every dialect (JS: two Numbers). Its own arm so that it
  -- does not depend on the dialect split in the generic `==` arm below, and
  -- `Refine.applyBinop_int_eq` stays `rfl` for an arbitrary dialect.
  | "==", .int x, .int y => .val (.bool (x == y))
  | "!=", .int x, .int y => .val (.bool (!(x == y)))
  -- `==` on strings compares contents in Python and addresses in C. `Val.beq` is
  -- structural, so it is right for Python and wrong for C.
  | "==", .str _, .str _ =>
      if d.stringsAreValues then .val (.bool (Val.beq a b))
      else .hole "str:pointer-equality-not-modelled"
  | "!=", .str _, .str _ =>
      if d.stringsAreValues then .val (.bool (!Val.beq a b))
      else .hole "str:pointer-equality-not-modelled"
  -- Floats, including mixed `int`/`float`. Placed before the generic `==`/`!=` so that
  -- the dialect split on comparison (see `flCmp`) is not bypassed by `Val.beq`.
  | op, .float _, .float _ => flBinop d op a b
  | op, .float _, .int _   => flBinop d op a b
  | op, .int _,   .float _ => flBinop d op a b
  -- Floor division. Distinct from `/` on purpose: Python's `/` is *true* division and
  -- `//` floors. The transpiler currently maps `//` onto `"/"` (see the note on
  -- `applyBinop_py_div`), so `"//"` is unreachable from the present corpora and exists so
  -- that the transpiler can start emitting the two separately.
  | "//", .int x, .int y => numToE (nc.div x y)
  -- `006-reduce-remaining-holes`, Story 5: interior-pointer arithmetic and
  -- comparison. Placed BEFORE the generic `"==",x,y`/`"!=",x,y` catch-all just
  -- below, deliberately: those would otherwise route an `.iref`/`.iref` pair
  -- through `Val.beq`, whose own wildcard (`Syntax.lean`) answers `false`
  -- unconditionally, silently wrong for FR-013's own "cross-object `==` is
  -- well-defined, not a hole" requirement.
  --
  -- Same-object arithmetic/subtraction/ordering succeed (an array's elements
  -- only -- a struct FIELD's address has no `+`/`-`/ordering in standard C, so a
  -- `.fld` selector on either side of one of those three stays a hole, `Sel`'s own
  -- doc comment's reasoning). Cross-object arithmetic, subtraction and ordering
  -- (undefined behaviour in C itself) become a DYNAMIC hole -- evaluation-time, not
  -- export-time, mirroring the already-shipped `.str`/`.str` `.cLike`
  -- "pointer-arithmetic/-compare-not-modelled" precedent just above. Equality and
  -- inequality are NOT gated on same-object: comparing addresses for equality
  -- across two different objects is well-defined in C (it is only ordering and
  -- subtraction across objects that are UB), so `==`/`!=` answer directly from
  -- `(ref, selector)` structural equality regardless of which object each side
  -- names.
  | "+", .iref r sel, .int n =>
      match sel with
      | .idx i => .val (.iref r (.idx (i + n)))
      | .fld _ => .hole "iref:arith-on-field"
  | "+", .int n, .iref r sel =>
      match sel with
      | .idx i => .val (.iref r (.idx (i + n)))
      | .fld _ => .hole "iref:arith-on-field"
  | "-", .iref r sel, .int n =>
      match sel with
      | .idx i => .val (.iref r (.idx (i - n)))
      | .fld _ => .hole "iref:arith-on-field"
  | "-", .iref r1 s1, .iref r2 s2 =>
      if r1 != r2 then .hole "iref:cross-object"
      else match s1, s2 with
           | .idx i, .idx j => numToE (nc.sub i j)
           | _,      _      => .hole "iref:sub-non-index"
  | "<",  .iref r1 s1, .iref r2 s2 =>
      if r1 != r2 then .hole "iref:cross-object"
      else match s1, s2 with
           | .idx i, .idx j => .val (.bool (i < j))
           | _,      _      => .hole "iref:cmp-non-index"
  | "<=", .iref r1 s1, .iref r2 s2 =>
      if r1 != r2 then .hole "iref:cross-object"
      else match s1, s2 with
           | .idx i, .idx j => .val (.bool (i ≤ j))
           | _,      _      => .hole "iref:cmp-non-index"
  | ">",  .iref r1 s1, .iref r2 s2 =>
      if r1 != r2 then .hole "iref:cross-object"
      else match s1, s2 with
           | .idx i, .idx j => .val (.bool (i > j))
           | _,      _      => .hole "iref:cmp-non-index"
  | ">=", .iref r1 s1, .iref r2 s2 =>
      if r1 != r2 then .hole "iref:cross-object"
      else match s1, s2 with
           | .idx i, .idx j => .val (.bool (i ≥ j))
           | _,      _      => .hole "iref:cmp-non-index"
  | "==", .iref r1 s1, .iref r2 s2 => .val (.bool (r1 == r2 && s1 == s2))
  | "!=", .iref r1 s1, .iref r2 s2 => .val (.bool !(r1 == r2 && s1 == s2))
  -- JavaScript `==`/`!=` is LOOSE equality (`1 == "1"` is `true`), which `Val.beq`
  -- answered `false`. Same-type operands are decided; cross-type coercion is a hole.
  -- (`int`/`int`, `str`/`str` and the float arms above are already right for JS.)
  | "==", x, y           =>
      match d with
      | .javascript => jsEqE false false x y
      | _           => binopFallback d op x y
  | "!=", x, y           =>
      match d with
      | .javascript => jsEqE false true x y
      | _           => binopFallback d op x y
  -- Everything else: structural `==`/`!=`, `&&`/`||` (reached only when the left
  -- operand did not decide the result, so the value is the RIGHT operand under value
  -- semantics), a `bool` promoted under `.cLike`, or a hole. See `binopFallback`.
  | _, _, _              => binopFallback d op a b

/-!
### Operator equations

Refinement proofs need `applyBinop` to reduce cleanly. For the unbounded (Python) config
these are definitional; for fixed-width configs they are *conditional on
representability*, which is the whole point — a C function only agrees with its
mathematical model where nothing overflows.
-/

@[simp] theorem applyBinop_py_add (x y : Int) :
    applyBinop .python "+" (.int x) (.int y) = .val (.int (x + y)) := rfl
@[simp] theorem applyBinop_py_sub (x y : Int) :
    applyBinop .python "-" (.int x) (.int y) = .val (.int (x - y)) := rfl
@[simp] theorem applyBinop_py_mul (x y : Int) :
    applyBinop .python "*" (.int x) (.int y) = .val (.int (x * y)) := rfl
@[simp] theorem applyBinop_py_div (x y : Int) (h : y ≠ 0) :
    applyBinop .python "/" (.int x) (.int y) = .val (.int (Int.fdiv x y)) := by
  simp [applyBinop, numToE, Dialect.toNumConfig, NumConfig.div, NumConfig.quot,
        NumConfig.finish, NumConfig.python, IntType.inRange, IntType.wrap_unbounded, h]
@[simp] theorem applyBinop_py_mod (x y : Int) (h : y ≠ 0) :
    applyBinop .python "%" (.int x) (.int y) = .val (.int (Int.fmod x y)) := by
  simp [applyBinop, numToE, Dialect.toNumConfig, NumConfig.mod, NumConfig.quot,
        NumConfig.rem, NumConfig.finish, NumConfig.python, IntType.inRange, IntType.wrap_unbounded, h]
@[simp] theorem applyBinop_py_divZero (x : Int) :
    applyBinop .python "/" (.int x) (.int 0) = .exn (.str "ZeroDivisionError") := rfl
@[simp] theorem applyBinop_py_modZero (x : Int) :
    applyBinop .python "%" (.int x) (.int 0) = .exn (.str "ZeroDivisionError") := rfl

/-! ### The two measured JS bugs (research.md / docs/languages.md), checked here rather
than only in a real corpus, whose export shape may or may not exercise them. -/

/-- Node: `0 || 5` is `5`. Under the OLD `.cLike`-routed dialect this returned a coerced
`Val.bool`, a confirmed wrong answer. `Val`/`EResult` have no `DecidableEq` (`Syntax.lean`
derives only `Repr, Inhabited` for both), so this is `rfl`, not `decide` — matching how
`applyBinop_py_add` etc. above are proved. -/
example : applyBinop .javascript "||" (.int 0) (.int 5) = .val (.int 5) := rfl
#eval applyBinop .javascript "||" (.int 0) (.int 5)   -- val (int 5), matches Node

/-- Node: `1 && 0` is `0` (the second operand, since the first is truthy). -/
example : applyBinop .javascript "&&" (.int 1) (.int 0) = .val (.int 0) := rfl
#eval applyBinop .javascript "&&" (.int 1) (.int 0)   -- val (int 0), matches Node

/-- Node: `2147483647 + 1 === 2147483648`. Under the OLD `.cLike`-routed dialect this
wrapped to `-2147483648`, the same confirmed-wrong answer `applyBinop_c_add` above would
give (32-bit wraparound). -/
example : applyBinop .javascript "+" (.int 2147483647) (.int 1) = .val (.int 2147483648) := rfl
#eval applyBinop .javascript "+" (.int 2147483647) (.int 1)  -- val (int 2147483648)

/-! `/` and `%`: the `docs/languages.md` §2/§3 rows, which the `.javascript` dialect
first got wrong by inheriting Python's floor (`-7 % 3` was `2`, `7 / 2` was `3`). -/
example : applyBinop .javascript "%" (.int (-7)) (.int 3) = .val (.int (-1)) := rfl
example : applyBinop .javascript "%" (.int 7) (.int (-3)) = .val (.int 1) := rfl
example : applyBinop .javascript "/" (.int 6) (.int (-3)) = .val (.int (-2)) := rfl
#eval applyBinop .javascript "%" (.int (-7)) (.int 3)   -- val (int (-1)), matches Node
#eval applyBinop .javascript "/" (.int 7) (.int 2)      -- val (float 3.5), matches Node
#eval applyBinop .javascript "/" (.int (-7)) (.int 2)   -- val (float -3.5), matches Node
#eval applyBinop .javascript "/" (.int 5) (.int 0)      -- val (float +inf), matches Node
#eval applyBinop .javascript "%" (.int 5) (.int 0)      -- val (float NaN), matches Node
#eval applyBinop .javascript "%" (.int (-6)) (.int 3)   -- val (float -0), matches Node
#eval applyBinop .javascript "%" (.float (Fl.ofBits (Float.toBits (-7.5)).toNat)) (.int 2)
  -- val (float -1.5), matches Node (CPython's floored `%` gives 0.5)
#eval applyBinop .javascript "||" (.float (Fl.ofBits (Float.toBits 0.0).toNat)) (.int 2)
  -- val (int 2), matches Node's `0.0 || 2` (was `bool true`)

/-! Java `%` on doubles is the TRUNCATED remainder (JLS 15.17.3): `-5.5 % 2.0` is `-1.5`.
`.cLike` used CPython's floored `pyMod` and answered `0.5`. Pinned by `#guard`, which
compares the IEEE bits, so a regression fails the build. -/
#guard (match applyBinop .cLike "%" (.float (Fl.ofBits (Float.toBits (-5.5)).toNat))
                                     (.float (Fl.ofBits (Float.toBits 2.0).toNat)) with
        | .val (.float f) => f.bits == (Float.toBits (-1.5)).toNat
        | _ => false)
#guard (match applyBinop .cLike "%" (.float (Fl.ofBits (Float.toBits 5.5).toNat))
                                     (.int (-2)) with
        | .val (.float f) => f.bits == (Float.toBits 1.5).toNat
        | _ => false)
-- CPython is unchanged: `-5.5 % 2.0 == 0.5`.
#guard (match applyBinop .python "%" (.float (Fl.ofBits (Float.toBits (-5.5)).toNat))
                                      (.float (Fl.ofBits (Float.toBits 2.0).toNat)) with
        | .val (.float f) => f.bits == (Float.toBits 0.5).toNat
        | _ => false)

/-! `==` vs `===` (`docs/languages.md` §4). Every right-hand side below is Node's answer,
from `node -e` (v22); a hole is written where Core declines to answer. -/
example : applyBinop .javascript "===" (.int 1) (.str "1") = .val (.bool false) := rfl
example : applyBinop .javascript "!==" (.int 1) (.str "1") = .val (.bool true) := rfl
example : applyBinop .javascript "===" (.int 1) (.int 1) = .val (.bool true) := rfl
example : applyBinop .javascript "===" (.str "a") (.str "a") = .val (.bool true) := rfl
example : applyBinop .javascript "===" (.bool true) (.int 1) = .val (.bool false) := rfl
example : applyBinop .javascript "===" .unit (.int 0) = .val (.bool false) := rfl
-- `1 == "1"` and `0 == false` are `true` in Node; Core used to say `false`. Now a hole:
example : applyBinop .javascript "==" (.int 1) (.str "1")
    = .hole "js:==:cross-type-coercion" := rfl
example : applyBinop .javascript "==" (.int 0) (.bool false)
    = .hole "js:==:cross-type-coercion" := rfl
-- `null == undefined` is `true`, `null == 0` is `false`, `null === undefined` is `false`
-- (Core cannot tell null from undefined, so `===` on two of them is a hole).
example : applyBinop .javascript "==" .unit .unit = .val (.bool true) := rfl
example : applyBinop .javascript "==" .unit (.int 0) = .val (.bool false) := rfl
example : applyBinop .javascript "!=" .unit (.str "") = .val (.bool true) := rfl
example : applyBinop .javascript "===" .unit .unit = .hole "js:===:null-vs-undefined" := rfl
-- same-type `==` is exact
example : applyBinop .javascript "==" (.bool true) (.bool true) = .val (.bool true) := rfl
example : applyBinop .javascript "==" (.int 2) (.int 3) = .val (.bool false) := rfl
-- objects: identity (`[1] == [1]` is `false`; `o == o` is `true`)
example : applyBinop .javascript "==" (.ref 0) (.ref 1) = .val (.bool false) := rfl
example : applyBinop .javascript "===" (.ref 4) (.ref 4) = .val (.bool true) := rfl
example : applyBinop .javascript "==" (.list [.int 1]) (.list [.int 1])
    = .hole "js:eq:object-identity-unknown" := rfl
-- `===` is not a JS-only spelling anywhere else: other dialects hole rather than guess.
example : applyBinop .python "===" (.int 1) (.int 1) = .hole "binop:===:non-javascript" := rfl
#eval applyBinop .javascript "===" (.int 1) (.float (Fl.ofBits (Float.toBits 1.0).toNat))
  -- val (bool true), matches Node's `1 === 1.0`
#eval applyBinop .javascript "===" (.float (Fl.ofBits (Float.toBits (0.0/0.0)).toNat))
                                   (.float (Fl.ofBits (Float.toBits (0.0/0.0)).toNat))
  -- val (bool false), matches Node's `NaN === NaN`
#eval applyBinop .javascript "===" (.float (Fl.ofBits (Float.toBits (-0.0)).toNat)) (.int 0)
  -- val (bool true), matches Node's `-0 === 0`

/-! Bitwise operators: ToInt32/ToUint32 (`jsBitwise`). Right-hand sides from `node -e`. -/
example : applyBinop .javascript "<<" (.int 1) (.int 31) = .val (.int (-2147483648)) := rfl
example : applyBinop .javascript "<<" (.int 1) (.int 32) = .val (.int 1) := rfl
example : applyBinop .javascript "<<" (.int 1) (.int 33) = .val (.int 2) := rfl
example : applyBinop .javascript "<<" (.int 1) (.int (-1)) = .val (.int (-2147483648)) := rfl
example : applyBinop .javascript "|" (.int 2147483648) (.int 0) = .val (.int (-2147483648)) := rfl
example : applyBinop .javascript "|" (.int 4294967296) (.int 0) = .val (.int 0) := rfl
example : applyBinop .javascript "^" (.int (-2147483649)) (.int 0) = .val (.int 2147483647) := rfl
example : applyBinop .javascript "&" (.int 5) (.int (-1)) = .val (.int 5) := rfl
example : applyBinop .javascript "&" (.int 4294967295) (.int 1) = .val (.int 1) := rfl
example : applyBinop .javascript ">>" (.int (-8)) (.int 1) = .val (.int (-4)) := rfl
example : applyBinop .javascript ">>" (.int 4294967295) (.int 0) = .val (.int (-1)) := rfl
example : applyBinop .javascript ">>>" (.int (-1)) (.int 0) = .val (.int 4294967295) := rfl
example : applyBinop .javascript ">>>" (.int (-1)) (.int 28) = .val (.int 15) := rfl
example : applyBinop .javascript ">>>" (.int (-16)) (.int 2) = .val (.int 1073741820) := rfl
example : applyBinop .javascript ">>>" (.int 3) (.int (-1)) = .val (.int 0) := rfl
example : applyBinop .javascript "|" (.int 9007199254740992) (.int 0) = .val (.int 0) := rfl
example : applyBinop .javascript "|" (.int 9007199254740994) (.int 0)
    = .hole "js:bitwise:operand-beyond-2^53" := rfl
-- C is untouched: `1 << 31` is still `INT_MIN` under `.cLike`, `~0` still `-1`.
example : applyBinop .cLike "<<" (.int 1) (.int 31) = .val (.int (-2147483648)) := rfl
#eval applyBinop .javascript ">>>" (.int (-1)) (.int 0)   -- val (int 4294967295), Node
#eval applyBinop .javascript "<<" (.int 1) (.int 32)       -- val (int 1), Node

/-! ### Float equations, and the two that must not regress

`Val.beq` on floats is the place where a plausible-looking implementation is wrong. Both
directions are pinned here, so that replacing `Fl.eqv` with structural bit equality — or
with `DecidableEq Fl`, which is derived and therefore always in scope — fails the build
rather than the oracle. This is the executable form of `Float.lean`'s
`float_beq_is_not_bit_equality`. -/

/-- **NaN is not equal to itself**, even though the two bit patterns are identical. -/
@[simp] theorem beq_float_nan_self :
    Val.beq (.float (Fl.nan Format.binary64)) (.float (Fl.nan Format.binary64)) = false := by
  decide

/-- **`-0.0` equals `+0.0`**, even though the two bit patterns differ. -/
@[simp] theorem beq_float_negzero :
    Val.beq (.float (Fl.zero Format.binary64 true))
            (.float (Fl.zero Format.binary64 false)) = true := by
  decide

/-- ...and they really are different bit patterns, so the theorem above has content. -/
theorem float_negzero_bits_differ :
    (Fl.zero Format.binary64 true).bits ≠ (Fl.zero Format.binary64 false).bits := by
  decide

/-- `-0.0` is false, like `0.0`. -/
@[simp] theorem truthy_float_negzero :
    Val.truthy (.float (Fl.zero Format.binary64 true)) = false := rfl

/-- Representability under the 32-bit signed C configuration. -/
abbrev Fits32 (x : Int) : Prop := IntType.inRange (.signed .w32) x = true

@[simp] theorem applyBinop_c_add {x y : Int} (h : Fits32 (x + y)) :
    applyBinop .cLike "+" (.int x) (.int y) = .val (.int (x + y)) := by
  simp [applyBinop, numToE, Dialect.toNumConfig, NumConfig.add, NumConfig.finish,
        NumConfig.c32Wrapv, NumConfig.c32, h]
@[simp] theorem applyBinop_c_sub {x y : Int} (h : Fits32 (x - y)) :
    applyBinop .cLike "-" (.int x) (.int y) = .val (.int (x - y)) := by
  simp [applyBinop, numToE, Dialect.toNumConfig, NumConfig.sub, NumConfig.finish,
        NumConfig.c32Wrapv, NumConfig.c32, h]
@[simp] theorem applyBinop_c_mul {x y : Int} (h : Fits32 (x * y)) :
    applyBinop .cLike "*" (.int x) (.int y) = .val (.int (x * y)) := by
  simp [applyBinop, numToE, Dialect.toNumConfig, NumConfig.mul, NumConfig.finish,
        NumConfig.c32Wrapv, NumConfig.c32, h]
@[simp] theorem applyBinop_c_div {x y : Int} (hy : y ≠ 0) (h : Fits32 (Int.tdiv x y)) :
    applyBinop .cLike "/" (.int x) (.int y) = .val (.int (Int.tdiv x y)) := by
  simp [applyBinop, numToE, Dialect.toNumConfig, NumConfig.div, NumConfig.quot,
        NumConfig.finish, NumConfig.c32Wrapv, NumConfig.c32, hy, h]
@[simp] theorem applyBinop_c_divZero (x : Int) :
    applyBinop .cLike "/" (.int x) (.int 0) = .exn (.str "ZeroDivisionError") := rfl

/-! `binopFallback` on operands it does not promote is `binopTail`, and `binopTail` on a
literal operator is one line. Stated as `simp` lemmas so that proofs which `simp` through
`applyBinop` (`Specs/V8Spec.lean`) see the same terms as before the fallback was split
out. -/
@[simp] theorem binopFallback_int_int (d : Dialect) (op : String) (x y : Int) :
    binopFallback d op (.int x) (.int y) = binopTail d op (.int x) (.int y) := rfl
@[simp] theorem binopTail_eq (d : Dialect) (a b : Val) :
    binopTail d "==" a b = .val (.bool (Val.beq a b)) := rfl
@[simp] theorem binopTail_ne (d : Dialect) (a b : Val) :
    binopTail d "!=" a b = .val (.bool (!Val.beq a b)) := rfl
@[simp] theorem binopTail_and (d : Dialect) (a b : Val) :
    binopTail d "&&" a b = .val (if d.boolOpsAreValues then b else .bool b.truthy) := rfl
@[simp] theorem binopTail_or (d : Dialect) (a b : Val) :
    binopTail d "||" a b = .val (if d.boolOpsAreValues then b else .bool b.truthy) := rfl

/-- The promoted arms of `applyBinop` compute exactly what the integer arms do. -/
theorem cIntBinop_eq (op : String) (x y : Int) (h : op ∈ cIntOps) :
    cIntBinop op x y = applyBinop .cLike op (.int x) (.int y) := by
  simp only [cIntOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> rfl

/-! The SQLite fixture of `docs/scale.md`, at the operator level: `(a < b) == 1` is true
and `(a < b) + (b < a)` is `1` under `.cLike`, as `cc` computes. -/
example : applyBinop .cLike "==" (.bool true) (.int 1) = .val (.bool true) := rfl
example : applyBinop .cLike "+" (.bool true) (.bool false) = .val (.int 1) := rfl
example : applyBinop .cLike "*" (.int 7) (.bool true) = .val (.int 7) := rfl
-- Java's logical `&` on two `boolean`s stays a `boolean`.
example : applyBinop .cLike "&" (.bool true) (.bool false) = .val (.bool false) := rfl
-- Python is untouched by this change (its own `True == 1` is a separate matter).
example : applyBinop .python "+" (.bool true) (.int 1) = .hole "binop:+" := rfl

/-- Built-in unary operators. -/
def applyUnop (d : Dialect) (op : String) (a : Val) : EResult :=
  match op, a with
  -- Negation goes through `NumConfig` for the same reason the binary operators do:
  -- `-INT_MIN` is not representable, so under a fixed-width dialect it must wrap, trap,
  -- or become a hole — never the unrepresentable number. This path was left unchecked
  -- when `Numeric` was first wired in, and `Autoform/Refine.lean` caught it.
  | "-", .int x => numToE ((d.toNumConfig).neg x)
  -- Float negation is a sign-bit flip: exact, no rounding, and correct on `-0.0` and NaN
  -- where "subtract from zero" would not be (`0.0 - 0.0 = 0.0`, but `-(0.0) = -0.0`).
  | "-", .float f => .val (.float f.neg)
  | "!", x      => .val (.bool (!x.truthy))
  -- `~x` — **bitwise** complement, which is not `!x`. Joern spells the two
  -- `<operator>.not` and `<operator>.logicalNot`; this exporter previously mapped *both*
  -- onto `"!"`, so `~0` translated to `false`. `bnot` is `-x-1` wrapped to the dialect's
  -- width, which is two's complement at every width and never overflows.
  | "~", .int x =>
      match d with
      | .javascript => jsBitNot x            -- `~2147483648` is `2147483647` in Node
      | _           => numToE ((d.toNumConfig).bnot x)
  -- A `bool` operand is promoted to 0/1 under `.cLike` (see `Dialect.promotesBool`):
  -- `-(a < b)` is `-1` in C. Elsewhere it stays the hole it was.
  | "-", .bool b => if d.promotesBool then numToE ((d.toNumConfig).neg (boolToInt b))
                    else .hole s!"unop:{op}"
  | "~", .bool b => if d.promotesBool then numToE ((d.toNumConfig).bnot (boolToInt b))
                    else .hole s!"unop:{op}"
  -- **Width conversions.** `static_cast<uint8_t>(e)` in C++ is a unary operator whose
  -- meaning is completely determined: since C++20, conversion to any integer type is
  -- two's-complement reduction modulo `2^width`, which is exactly `IntType.wrap`. So it
  -- gets an operator here rather than a constructor in `Syntax.lean` — a cast *is* a
  -- unary operator, and spelling it as one means `Expr.hole`-freedom, fuel monotonicity,
  -- rendering and the ledger all keep working without a single new case anywhere.
  --
  -- What is deliberately **not** here:
  --
  -- * a cast to `char`, whose signedness is implementation-defined, so
  --   `static_cast<char>(200)` has no standard-mandated value;
  -- * a cast to `double`, which rounds rather than truncates and belongs to `Fl`;
  -- * a cast between *pointer* types, which reinterprets an address — and Core has no
  --   addresses. The exporter keeps that one as an `op:cast:pointer` hole. Collapsing the
  --   two would be the `<operator>.and` mistake again: same syntax, different operation.
  --
  -- A non-integer operand falls through to the hole below, labelled `unop:cast:u8` and
  -- so on, which is the honest answer for `static_cast<int>(someDouble)`.
  | "cast:i8",  .int x => .val (.int (IntType.wrap (.signed .w8) x))
  | "cast:u8",  .int x => .val (.int (IntType.wrap (.unsigned .w8) x))
  | "cast:i16", .int x => .val (.int (IntType.wrap (.signed .w16) x))
  | "cast:u16", .int x => .val (.int (IntType.wrap (.unsigned .w16) x))
  | "cast:i32", .int x => .val (.int (IntType.wrap (.signed .w32) x))
  | "cast:u32", .int x => .val (.int (IntType.wrap (.unsigned .w32) x))
  | "cast:i64", .int x => .val (.int (IntType.wrap (.signed .w64) x))
  | "cast:u64", .int x => .val (.int (IntType.wrap (.unsigned .w64) x))
  -- A `bool` converts to 1/0 at any width, in every dialect.
  | "cast:i8",  .bool b => .val (.int (if b then 1 else 0))
  | "cast:u8",  .bool b => .val (.int (if b then 1 else 0))
  | "cast:i16", .bool b => .val (.int (if b then 1 else 0))
  | "cast:u16", .bool b => .val (.int (if b then 1 else 0))
  | "cast:i32", .bool b => .val (.int (if b then 1 else 0))
  | "cast:u32", .bool b => .val (.int (if b then 1 else 0))
  | "cast:i64", .bool b => .val (.int (if b then 1 else 0))
  | "cast:u64", .bool b => .val (.int (if b then 1 else 0))
  -- The C address model (`Address.lean`): a cast to a pointer type whose operand's
  -- static type was not resolved -- the identity on pointer values, a hole on a
  -- non-zero integer. Pointer-to-INTEGER casts are the `cast:<w>` arms above, which
  -- have no case for a pointer value and so stay holes: Core blocks have no address.
  | "cast:ptr", v => ptrCast v
  -- `-`/`~` at a typed width (`"-:u32"`, `"~:i64"`; `TypedInt.lean`).
  | _, _        => match typedIntUnop op a with
                   | some r => r
                   | none   => .hole s!"unop:{op}"

/-- `static_cast<uint8_t>` is reduction mod 256, stated against `IntType.wrap` rather
than against `applyUnop`'s own definition. -/
@[simp] theorem applyUnop_cast_u8 (d : Dialect) (x : Int) :
    applyUnop d "cast:u8" (.int x) = .val (.int (x % 256)) := by
  cases d <;> rfl

/-- The narrowing is real: `static_cast<uint8_t>(300)` is `44`, not `300`. A cast that
returned its argument — or a hole — would make every downstream theorem about a
converting program vacuously true, so this is checked by evaluation. -/
example : applyUnop .cLike "cast:u8" (.int 300) = .val (.int 44) := by rfl

/-- And it is not the identity on the signed side either: `static_cast<int8_t>(200)` is
`-56`. -/
example : applyUnop .cLike "cast:i8" (.int 200) = .val (.int (-56)) := by rfl

/-- A cast of something that is not a number is a hole, not a guess. -/
example : applyUnop .cLike "cast:u8" (.str "x") = .hole "unop:cast:u8" := by rfl

/-- JS `~` is `-ToInt32(x) - 1` (`jsBitNot`); Node: `~2147483648` is `2147483647`, `~0`
is `-1`. The unbounded `NumConfig.python` answer was `-2147483649`. -/
example : applyUnop .javascript "~" (.int 2147483648) = .val (.int 2147483647) := rfl
example : applyUnop .javascript "~" (.int 0) = .val (.int (-1)) := rfl

/-- Negation is definitional under the unbounded (Python) config. -/
@[simp] theorem applyUnop_py_neg (x : Int) :
    applyUnop .python "-" (.int x) = .val (.int (-x)) := rfl

/-- Under a fixed-width dialect negation only equals mathematical negation where the
result is representable. `-INT_MIN` is precisely where it does not. -/
@[simp] theorem applyUnop_c_neg {x : Int} (h : Fits32 (-x)) :
    applyUnop .cLike "-" (.int x) = .val (.int (-x)) := by
  simp [applyUnop, numToE, Dialect.toNumConfig, NumConfig.neg, NumConfig.finish,
        NumConfig.c32Wrapv, NumConfig.c32, h]

/-- Unary minus on a float is a sign flip, in every dialect — no rounding, and correct on
`-0.0` and NaN, where "subtract from zero" would not be. -/
@[simp] theorem applyUnop_float_neg (d : Dialect) (f : Fl) :
    applyUnop d "-" (.float f) = .val (.float f.neg) := by cases d <;> rfl


/-- Membership test. -/
def valIn (x c : Val) : EResult :=
  -- An instance of a class with a builtin base is a container: `0 in A((0,))` is `True`
  -- in CPython for `class A(tuple)`. `unbuiltin` is non-recursive, which keeps this
  -- function non-recursive too.
  match c.unbuiltin with
  | .list vs  => .val (.bool (vs.any (Val.beq x)))
  | .tuple vs => .val (.bool (vs.any (Val.beq x)))
  | .dict kvs => .val (.bool (kvs.any (fun kv => Val.beq x kv.1)))
  | .str s    => match x with
                 | .str t => .val (.bool ((s.splitOn t).length > 1))
                 | _      => .hole "in:non-str-in-str"
  | _         => .hole "in:non-container"

/-- Function table, keyed by name. -/
abbrev FuncTable := List (String × Func)

/-- Everything the interpreter needs: the callable functions and the source dialect. -/
structure Ctx where
  dialect : Dialect
  table   : FuncTable
  /-- Classes whose base is a builtin type — see `Program.builtinBases`. -/
  builtinBases : List (String × BuiltinBase) := []
  /-- Heap address of the module-level bindings frame. Globals must be mutable and must
  outlive any single call, so they live on the heap rather than in `Env`. -/
  globals : Ref := 0
  /-- The Python class table — see `Program.pyClasses`. `none` keeps the legacy
  name-suffix resolution; `some` selects Python's own lookup rules (`Ctx.pyStrict`). -/
  pyClasses : Option (List PyClass) := none

/-- Build a function table from a program. -/
def Program.table (p : Program) : FuncTable := p.funcs.map (fun f => (f.name, f))

/-- Resolve a callable by exact name, else by suffix.

Joern emits fully-qualified names like `pkg/mod.py:<module>.Cls.meth`, while call sites
carry only the short name. Suffix matching is a *heuristic*, and an ambiguous or missing
resolution becomes a hole rather than a guess. -/
def Ctx.resolve (ctx : Ctx) (n : String) : Option Func :=
  match ctx.table.find? (·.1 == n) with
  | some (_, f) => some f
  | none        =>
    -- Scan for a *unique* suffix match, stopping as soon as a second one is seen.
    -- The previous form built the full match list with `filter`, so every miss
    -- allocated across the whole table — on Django's 10,623 functions that made the
    -- ledger run 363s, 55x the cost of a corpus 5x smaller. This is still linear per
    -- lookup (the asymptotic fix is an index on `Ctx`, recorded as an open item), but
    -- it no longer allocates and it exits early on the ambiguous case.
    let suffix := "." ++ n
    let rec go : FuncTable → Option Func → Option Func
      | [],           acc      => acc
      | (k, f) :: ps, none     => if k.endsWith suffix then go ps (some f) else go ps none
      | (k, _) :: ps, some f   => if k.endsWith suffix then none else go ps (some f)
    go ctx.table none

/-! ## The calling convention

`f(*xs, k=v, **d)` and `def f(a, *args, **kwargs)` are one mechanism, split across two
places: `evalList` turns an argument list into a **positional list plus a keyword list**,
and `bindParams` turns those two lists plus a `Func`'s parameter description into an
environment.

Both halves are ordinary total functions — `bindParams` is not even recursive on fuel —
so the interpreter's seven-way mutual recursion is unchanged in shape and
`Autoform/FuelMono.lean` still covers exactly the same functions. -/

/-- View a value as keyword bindings, for `**e`. Only a `dict` whose keys are *all*
strings qualifies: CPython raises `TypeError: keywords must be strings` otherwise, and
`argument after ** must be a mapping` for a non-`dict`, so `none` here means "raise",
never "ignore". -/
def strKeyed : Val → Option (List (String × Val))
  | .dict kvs =>
      kvs.foldr (fun kv acc =>
        match kv.1, acc with
        | .str k, some rest => some ((k, kv.2) :: rest)
        | _,      _         => none) (some [])
  | _ => none

/-- The parameters that receive positional arguments: every parameter except the
variadic and the keyword-only ones. -/
def Func.posParams (fn : Func) : List String :=
  fn.params.filter fun p => fn.vararg != some p && fn.kwarg != some p && !fn.kwonly.contains p

/-- The parameters a **keyword** argument may bind: the positional ones that are not
positional-only, then the keyword-only ones. A keyword naming anything else goes to
`**kwargs`, or is rejected (`kwargsRejected`). -/
def Func.kwParams (fn : Func) : List String :=
  fn.posParams.filter (fun p => !fn.posonly.contains p) ++ fn.kwonly

/-- The value of a literal, exactly as `evalExpr` gives it. -/
def Lit.toVal : Lit → Val
  | .int i   => .int i
  | .str s   => .str s
  | .bool b  => .bool b
  | .float f => .float f
  | .unit    => .unit

/-- The value of a default expression **when evaluating it once at `def` time and
evaluating it again at every call cannot be told apart**: a literal, or a tuple of
literals. Both denote immutable values with no identity Core can observe, so binding the
value per call is exactly CPython's evaluate-once rule.

Anything else is `none`, and deliberately so. `def f(x=[])` evaluates `[]` once and every
call shares that one list — the mutable-default aliasing every Python programmer meets
once — and `def f(t=time.monotonic)` reads `time` at definition time. Re-evaluating either
per call is the silently-wrong translation; `Func.defaultHole` turns it into a hole on
exactly the calls that need the default. -/
def defaultVal? : Expr → Option Val
  | .lit l     => some l.toVal
  | .tupleE es => (es.mapM fun (e : Expr) => match e with
                                    | .lit l => some l.toVal
                                    | _      => none).map .tuple
  | _          => none

/-- Was parameter `p` given a value by this call — positionally, or by a keyword that is
allowed to bind it? -/
def Func.supplied (fn : Func) (vs : List Val) (kws : List (String × Val)) (p : String) :
    Bool :=
  (fn.posParams.take vs.length).contains p || (fn.kwParams.contains p && kws.any (·.1 == p))

/-- Bindings for the parameters this call leaves unsupplied whose default is a
`defaultVal?` constant. Empty — by its first branch, so that it reduces without looking at
`params` — for every function with no recorded defaults, which is every function rendered
before defaults were modelled. -/
def Func.defaultEnv (fn : Func) (vs : List Val) (kws : List (String × Val)) : Env :=
  if fn.defaults.isEmpty then [] else
  fn.params.filterMap fun p =>
    if fn.supplied vs kws p then none else
    match fn.defaults.lookup p with
    | some e => (defaultVal? e).map (p, ·)
    | none   => none

/-- The first unsupplied parameter whose default is **not** a constant, as a hole label —
the default's own hole label if it is one (the exporter writes
`param:default-nonliteral` there), else `param:default-unsupported`. `none` when every
default this call needs is a constant. -/
def Func.defaultHole (fn : Func) (vs : List Val) (kws : List (String × Val)) :
    Option String :=
  if fn.defaults.isEmpty then none else
  fn.params.findSome? fun p =>
    if fn.supplied vs kws p then none else
    match fn.defaults.lookup p with
    | some e => match defaultVal? e with
                | some _ => none
                | none   => some (e.holes.headD "param:default-unsupported")
    | none   => none

/-- The statement a call actually runs: the body, unless the call needs a default Core
cannot evaluate, in which case it is that hole. Pure and fuel-free, so it adds nothing to
the interpreter's mutual recursion. -/
def Func.guardedBody (fn : Func) (vs : List Val) (kws : List (String × Val)) : Stmt :=
  match fn.defaultHole vs kws with
  | some l => .hole l
  | none   => fn.body

/-- The function name and captured environment of a closure value; `none` for anything
else. Named so that `Expr.call` can test for a closure-valued local with a two-way match
instead of a wildcard over every `Val` constructor. -/
def Val.closParts? : Val → Option (String × List (String × Val))
  | .clos g cap => some (g, cap)
  | _           => none

/-- Bind a call's arguments into the callee's environment.

The rule is CPython's:

* positional arguments fill `posParams` left to right (keyword-only parameters are not
  among them);
* leftovers go to `vararg` as a `tuple` — an empty one when there are none, which is
  why `def f(*a)` called with no arguments binds `a` to `()` rather than to `unit`;
* a keyword argument naming a `kwParams` parameter binds that parameter (a
  positional-only parameter is not among them);
* every other keyword argument goes to `kwarg` as a `dict` with `str` keys;
* an unsupplied parameter with a constant default sees that default
  (`Func.defaultEnv`). The defaults sit *under* the call's own bindings, in the base
  environment, so a supplied argument always shadows its default.

Departures, recorded rather than hidden:

* **Surplus positional arguments** with no `*args` are rejected by `posRejected` before
  the body runs, so the truncation here is never observable.
* **A keyword argument matching no parameter** with no `**kwargs` is dropped here and
  rejected by `kwargsRejected`, likewise never observable.
* **An unsupplied parameter with no default** is still left unbound (it reads `unit`),
  where CPython raises `TypeError: missing required argument`. A function rendered
  before defaults were recorded cannot be told apart from one that has none, so raising
  would reject calls CPython accepts. -/
def bindParams (fn : Func) (base : Env) (vs : List Val)
    (kws : List (String × Val)) : Env :=
  let ps    := fn.posParams
  let kp    := fn.kwParams
  let ρ₀    := (ps.zip vs).foldl (fun (e : Env) (x, v) => Env.set e x v)
                 (fn.defaultEnv vs kws ++ base)
  let rest  := vs.drop ps.length
  let ρ₁    := match fn.vararg with
               | some a => Env.set ρ₀ a (.tuple rest)
               | none   => ρ₀
  let named := kws.filter (fun kv => kp.contains kv.1)
  let extra := kws.filter (fun kv => !kp.contains kv.1)
  let ρ₂    := named.foldl (fun (e : Env) (x, v) => Env.set e x v) ρ₁
  match fn.kwarg with
  | some k => Env.set ρ₂ k (.dict (extra.map fun kv => (.str kv.1, kv.2)))
  | none   => ρ₂

/-- Does this call pass **more positional arguments than the callee can accept**?

CPython: `def f(a, b)` called as `f(1, 2, 3)` is
`TypeError: f() takes 2 positional arguments but 3 were given` (3.9.6). Core used to
truncate — `params.zip vs` drops the surplus — and the disagreement was recorded as the
theorem `surplusPositional_is_a_known_divergence`, now
`CallingConvention.surplusPositional_now_agrees_with_cpython`. Truncation is the dangerous
direction: a call the real program rejects loudly runs to completion in Core and every
theorem about it is a theorem about a program CPython never executes.

Keyword-only parameters do not count: `def f(a, *, b)` called as `f(1, 2)` is a
`TypeError` in CPython, and is here.

Only a *surplus* is rejected; see `bindParams` for why a shortfall is not.

A `*args` parameter absorbs any surplus, so a callee with `vararg` is never rejected. -/
def posRejected (fn : Func) (vs : List Val) : Bool :=
  fn.vararg.isNone && fn.posParams.length < vs.length

/-- A call passing no more arguments than the callee has positional parameters is never
rejected — in particular the zero-argument call, which is what most callers in a rendered
corpus are. -/
@[simp] theorem posRejected_nil (fn : Func) : posRejected fn [] = false := by
  simp [posRejected]

/-- `posRejected` on the shape a rendered corpus actually presents: a `Func` literal with
every calling-convention field at its default. The companion of `bindParams_mk`, and
needed for the same reason — a proof about a literal `Func` cannot fire a hypothesis-form
lemma without first deciding which `fn` it is about. -/
@[simp] theorem posRejected_mk (name : String) (params : List String) (body : Stmt)
    (vs : List Val) :
    posRejected ⟨name, params, body, none, none, [], [], []⟩ vs
      = decide (params.length < vs.length) := by
  have : (List.filter (fun p => none != some p) params) = params := by
    simp [List.filter_eq_self]
  simp [posRejected, Func.posParams, this]

/-- Does this call pass a keyword argument the callee cannot accept? CPython raises
`TypeError: f() got an unexpected keyword argument 'k'`; `bindParams` alone would silently
drop it, which is the silently-wrong shape this project keeps catching, so the check is
separate and `applyFunc` turns it into the exception. A keyword naming a positional-only
parameter is one of these, as in CPython. -/
def kwargsRejected (fn : Func) (kws : List (String × Val)) : Bool :=
  fn.kwarg.isNone && kws.any (fun kv => !fn.kwParams.contains kv.1)

/-- A call with no keyword arguments can never be rejected. -/
@[simp] theorem kwargsRejected_nil (fn : Func) : kwargsRejected fn [] = false := by
  simp [kwargsRejected]

/-- A function with no recorded defaults binds no defaults. -/
@[simp] theorem Func.defaultEnv_nil {fn : Func} (vs : List Val) (kws : List (String × Val))
    (hd : fn.defaults = []) : fn.defaultEnv vs kws = [] := by
  simp [Func.defaultEnv, hd]

/-- A function with no recorded defaults runs its body unchanged. -/
@[simp] theorem Func.guardedBody_nil {fn : Func} (vs : List Val) (kws : List (String × Val))
    (hd : fn.defaults = []) : fn.guardedBody vs kws = fn.body := by
  simp [Func.guardedBody, Func.defaultHole, hd]

/-- The literal form of `Func.guardedBody_nil`, for the same reason `bindParams_mk` exists. -/
@[simp] theorem Func.guardedBody_mk (name : String) (params : List String) (body : Stmt)
    (va kw : Option String) (ko po : List String) (vs : List Val)
    (kws : List (String × Val)) :
    Func.guardedBody ⟨name, params, body, va, kw, ko, po, []⟩ vs kws = body := rfl

/-- The literal form of `Func.defaultEnv_nil`. -/
@[simp] theorem Func.defaultEnv_mk (name : String) (params : List String) (body : Stmt)
    (va kw : Option String) (ko po : List String) (vs : List Val)
    (kws : List (String × Val)) :
    Func.defaultEnv ⟨name, params, body, va, kw, ko, po, []⟩ vs kws = [] := rfl

/-- A function with no variadic, keyword-only or defaulted parameters, called with no
keyword arguments, binds exactly what `applyFunc` bound before the calling convention
existed. This is the compatibility equation: every corpus rendered before starred
arguments, keyword-only parameters and defaults were modelled has all of those fields at
their defaults, so nothing about it changed. -/
theorem bindParams_plain {fn : Func} (base : Env) (vs : List Val)
    (h1 : fn.vararg = none) (h2 : fn.kwarg = none) (h3 : fn.kwonly = [])
    (h4 : fn.defaults = []) :
    bindParams fn base vs [] =
      (fn.params.zip vs).foldl (fun (e : Env) (x, v) => Env.set e x v) base := by
  have : (List.filter (fun p => none != some p) fn.params) = fn.params := by
    simp [List.filter_eq_self]
  simp [bindParams, Func.posParams, Func.defaultEnv, h1, h2, h3, h4, this]

/-- A function with **no parameters at all**, called with no keyword arguments, binds
nothing beyond `base` — whatever its other calling-convention fields say, because every
one of them is keyed by a parameter name. This is the form the generated accessor
theorems use (`SpecsGen/Basis.lean`): they already assume `fn.params = []`, so the fields
added after them need no new hypothesis. -/
theorem bindParams_noParams {fn : Func} (base : Env) (vs : List Val)
    (hp : fn.params = []) (h1 : fn.vararg = none) (h2 : fn.kwarg = none) :
    bindParams fn base vs [] = base := by
  simp [bindParams, Func.posParams, Func.defaultEnv, hp, h1, h2]

/-- The guard on a parameterless function is its body, for the same reason. -/
theorem Func.guardedBody_noParams {fn : Func} (vs : List Val) (kws : List (String × Val))
    (hp : fn.params = []) : fn.guardedBody vs kws = fn.body := by
  simp [Func.guardedBody, Func.defaultHole, hp]

/-- The same equation in the shape a rendered corpus actually presents: a `Func` literal
with every calling-convention field at its default. Stated separately because the
hypothesis form of `bindParams_plain` cannot fire on a literal without first deciding
which `fn` it is about. -/
@[simp] theorem bindParams_mk (name : String) (params : List String) (body : Stmt)
    (base : Env) (vs : List Val) :
    bindParams ⟨name, params, body, none, none, [], [], []⟩ base vs [] =
      (params.zip vs).foldl (fun (e : Env) (x, v) => Env.set e x v) base :=
  bindParams_plain base vs rfl rfl rfl rfl

/-- The short class name behind a class VALUE.

The exporter marks a class value by suffixing `<meta>` to the qualified name, and
`resolveMethod`/`classDefines` want the short name -- the last dotted segment. This cannot
split the whole name, because the FILE part contains dots
(`cachetools/__init__.py:<module>.Cache<meta>`). Named rather than inlined so that proofs
about the `mcall` case have a term to talk about. -/
def classNameOfValue (g : String) : String :=
  let base := if g.endsWith "<meta>" then g.dropRight 6 else g
  (base.splitOn ".").getLastD base

/-- Resolve a method on a class: prefer `Cls.meth`, else any `.meth`.

This is the **legacy** rule, kept for every program without a class table
(`Ctx.pyStrict` false): all non-Python corpora, and every Python export made before the
exporter recorded classes. It knows nothing of inheritance -- a subclass instance's
inherited method is found only through the any-`.meth` fallback, which takes *any*
unique function of that name, and a subclass override of a method the base calls on
`self` is reached only by accident. `docs/conformance.md` finding 3 is three wrong
answers it produced. -/
def Ctx.resolveMethodLegacy (ctx : Ctx) (cls meth : String) : Option Func :=
  match ctx.table.filter (fun p => p.1.endsWith ("." ++ cls ++ "." ++ meth)) with
  | (_, f) :: _ => some f
  | []          => ctx.resolve meth

/-! ### Python method resolution (STRATEGY.md §62)

With a class table (`Program.pyClasses`), a method is looked up the way CPython looks it
up on an instance: along `type(obj).__mro__`, the C3 linearisation of the class and its
bases, taking the first class that defines the name. Every step at which the table does
not determine the answer is a hole, never a guess:

* a class missing from the table (a test-suite subclass, a class the exporter dropped
  because its bases were not resolvable or its short name is ambiguous) —
  `mro:unknown-class:<C>`;
* a base from outside the corpus (`<ext>…`) reached before the name is found: Core does
  not know what `collections.abc.MutableMapping` defines — `mro:external-base:<B>.<m>`;
* a class-body binding that is not a plain `def` (`get = __getitem__`, `property`,
  `classmethod`) — `mro:class-attribute:<C>.<m>`;
* a C3 failure (CPython raises `TypeError` at class creation, so no instance exists) —
  also `mro:unknown-class`.

A name found nowhere along a fully-known MRO is *absent*: `object` defines it or nothing
does, and the callers keep their existing behaviour for that (`__init__` allocates a
plain object; any other method is the hole `mcall:<C>.<m>`). -/

/-- Python's own lookup rules are in force: a Python program carrying a class table. -/
def Ctx.pyStrict (ctx : Ctx) : Bool :=
  ctx.pyClasses.isSome && ctx.dialect == .python

/-- The table entry for a short class name. A name with two entries is not a class Core
can identify, so it is treated as missing (the exporter already drops such names; this
makes a hand-built table obey the same rule). -/
def Ctx.pyClass? (ctx : Ctx) (c : String) : Option PyClass :=
  match ctx.pyClasses with
  | none   => none
  | some t => match t.filter (·.name == c) with
              | [k] => some k
              | _   => none

/-- Prefix marking a base from outside the corpus. -/
def extBasePrefix : String := "<ext>"

/-- C3 merge: repeatedly take the first list head that is in no list's tail. `none` when
no head qualifies (an inconsistent hierarchy — CPython's `TypeError`) or the fuel, the
total length of the lists, runs out. -/
def c3Merge : Nat → List (List String) → Option (List String)
  | 0,   _  => none
  | n+1, ls =>
    let ls := ls.filter (fun l => !l.isEmpty)
    if ls.isEmpty then some [] else
    let good := ls.filterMap (fun l => match l with
                  | c :: _ => if ls.any (fun l' => (l'.drop 1).contains c) then none else some c
                  | []     => none)
    match good with
    | c :: _ => (c3Merge n (ls.map (fun l => l.filter (· != c)))).map (c :: ·)
    | []     => none

/-- The C3 linearisation of a class, by short name. An external base is a leaf: its own
ancestors are unknown, and since lookup stops at the first external class it reaches
(`Ctx.mroWalk`), the order of the classes *before* it is all that is ever used — and that
prefix does not depend on what comes after an external class in its own MRO, because no
corpus class can be an ancestor of an external one. -/
def Ctx.mroAux (ctx : Ctx) : Nat → String → Option (List String)
  | 0,   _ => none
  | n+1, c =>
    if c.startsWith extBasePrefix then some [c] else
    match ctx.pyClass? c with
    | none   => none
    | some k =>
      match k.bases.mapM (ctx.mroAux n) with
      | none    => none
      | some ls =>
        let lists := ls ++ [k.bases]
        (c3Merge (lists.foldl (fun a l => a + l.length) 0 + 1) lists).map (c :: ·)

/-- `type(obj).__mro__` for a class of the table, by short name. The fuel bounds the
inheritance depth by the number of classes, so a cyclic table is `none`, not a loop. -/
def Ctx.mro (ctx : Ctx) (c : String) : Option (List String) :=
  ctx.mroAux ((ctx.pyClasses.map List.length).getD 0 + 1) c

/-- Keys of the function table that are a method `m` defined directly in class `c`. -/
def Ctx.ownMethodKeys (ctx : Ctx) (c m : String) : List String :=
  (ctx.table.filter (fun p => p.1.endsWith ("." ++ c ++ "." ++ m))).map (·.1)

/-- Outcome of a method lookup along the MRO. -/
inductive MLookup where
  /-- Found: the qualified name of the defining function. -/
  | found  (q : String)
  /-- Not defined anywhere along a fully-known MRO. -/
  | absent
  /-- The table does not determine the answer. -/
  | hole   (l : String)
  deriving Repr, Inhabited, DecidableEq

/-- Walk an MRO (already computed) for method `m`. -/
def Ctx.mroWalk (ctx : Ctx) (m : String) : List String → MLookup
  | []      => .absent
  | c :: cs =>
    if c.startsWith extBasePrefix then
      .hole s!"mro:external-base:{c.drop extBasePrefix.length}.{m}"
    else
      let attrs := match ctx.pyClass? c with
                   | some k => k.attrs
                   | none   => []
      if attrs.contains m then .hole s!"mro:class-attribute:{c}.{m}" else
      match ctx.ownMethodKeys c m with
      | [q] => .found q
      | []  => ctx.mroWalk m cs
      | _   => .hole s!"mro:ambiguous-method:{c}.{m}"

/-- Look a method up on an instance of class `cls`, CPython's way. -/
def Ctx.lookupMethod (ctx : Ctx) (cls m : String) : MLookup :=
  match ctx.mro cls with
  | none   => .hole s!"mro:unknown-class:{cls}"
  | some l => ctx.mroWalk m l

/-- A function whose only behaviour is to be the hole `l`, whatever it is called with:
the variadic parameters accept any arguments, so `applyFunc` reaches the body, and the
body is the hole. It is how a method lookup the table cannot answer surfaces as a hole
at every call site without each one learning a new case. -/
def holeFunc (l : String) : Func :=
  { name := "<mro-hole>", params := ["<args>", "<kwargs>"], vararg := some "<args>"
  , kwarg := some "<kwargs>", body := .hole l }

/-- Method resolution under Python's rules. The reserved classes (`<module>…` module
objects, `<function>` boxed functions, `<local>` cells, `<globals>`) are not classes of
the program and keep `none`, which the callers already handle. -/
def Ctx.resolveMethodPy (ctx : Ctx) (cls meth : String) : Option Func :=
  if cls.startsWith "<" then none else
  match ctx.lookupMethod cls meth with
  | .found q => ctx.resolve q
  | .absent  => none
  | .hole l  => some (holeFunc l)

/-- Resolve a method on an instance of class `cls`: Python's MRO rules when the program
carries a class table, the legacy suffix rule otherwise. -/
def Ctx.resolveMethod (ctx : Ctx) (cls meth : String) : Option Func :=
  if ctx.pyStrict then ctx.resolveMethodPy cls meth else ctx.resolveMethodLegacy cls meth

/-- Method resolution for `obj.m(…)` on a heap object. Under Python's rules an attribute
in the INSTANCE's own `__dict__` shadows a method of its class (CPython consults the
instance dictionary before non-data class attributes), and such an attribute is called
without a receiver. Core does not call it -- it is the hole
`mcall:<C>.<m>:instance-attribute` -- but it no longer calls the class's method in its
place. Reserved classes and legacy programs are unchanged. -/
def Ctx.resolveMethodOn (ctx : Ctx) (o : Obj) (meth : String) : Option Func :=
  if ctx.pyStrict && !o.cls.startsWith "<" && o.fields.any (·.1 == meth) then
    some (holeFunc s!"mcall:{o.cls}.{meth}:instance-attribute")
  else ctx.resolveMethod o.cls meth

/-- With no instance attribute of that name, `obj.m` is the class's method, under either
rule. -/
theorem Ctx.resolveMethodOn_of_not_field {ctx : Ctx} {o : Obj} {m : String}
    (h : o.fields.any (·.1 == m) = false) :
    ctx.resolveMethodOn o m = ctx.resolveMethod o.cls m := by
  simp [Ctx.resolveMethodOn, h]

theorem Ctx.resolveMethodOn_of_none {ctx : Ctx} {o : Obj} {m : String}
    (h : ctx.pyClasses = none) : ctx.resolveMethodOn o m = ctx.resolveMethod o.cls m := by
  simp [Ctx.resolveMethodOn, Ctx.pyStrict, h]

/-- Does looking `meth` up on class `cls` *reach* something — a method, or a hole? The
guard for calling a method through a class value (`Base.m(self, …)`): under Python's
rules an inherited method counts; under the legacy rule only the class's own does
(`classDefines`, below), so that an unrelated global of that name is never taken. -/
def Ctx.classResponds (ctx : Ctx) (cls meth : String) : Bool :=
  if ctx.pyStrict then
    (match ctx.lookupMethod cls meth with
     | .absent => false
     | _       => true)
  else ctx.table.any (fun p => p.1.endsWith ("." ++ cls ++ "." ++ meth))

/-! ### `super()`

The exporter lowers zero-argument `super()` in a method of class `C` to
`super("C", self)` — CPython's own meaning of it, since the compiler supplies `__class__`
and the first argument. The call evaluates to an inert proxy value (a `Val.clos` under a
reserved name no source can spell: a field read on it is a `non-object` hole, calling it
resolves to nothing), and `obj.m(…)` on the proxy looks `m` up along
`type(self).__mro__` **after** `C`, then calls it with `self` as the receiver. -/

/-- Reserved function name of a `super()` proxy. -/
def superProxyName : String := "<super>"

/-- Build a `super(C, self)` proxy, when this is that call under Python's rules. The class
may arrive as a string (the exporter's lowering) or as a class value (`super(C, self)`
written out, where `C` evaluates to the class's `<meta>` value). -/
def Ctx.makeSuper (ctx : Ctx) (f : String) (vs : List Val) : Option Val :=
  if ctx.pyStrict && f == "super" then
    match vs with
    | [.str c, s] => some (.clos superProxyName [("__thisclass__", .str c), ("__self__", s)])
    | [.fn g,  s] => some (.clos superProxyName
                             [("__thisclass__", .str (classNameOfValue g)), ("__self__", s)])
    | _           => none
  else none

/-- The class and receiver of a `super()` proxy. -/
def superParts? : Val → Option (String × Val)
  | .clos g [("__thisclass__", .str c), ("__self__", s)] =>
      if g == superProxyName then some (c, s) else none
  | _ => none

/-- Where `super(C, self).m` lands: the qualified name of the method, or a hole. `self`'s
class is its heap object's class or its `bobj` class; an instance carrying captured
bindings (a function-local class) is refused, because the ancestor's method may close over
a different scope than the instance's class did. -/
def Ctx.superTarget (ctx : Ctx) (h : Heap) (c : String) (s : Val) (m : String) :
    Except String String :=
  let tp : Option String := match s with
    | .ref r    => match h.get r with
                   | some o => if o.captured.isEmpty then some o.cls else none
                   | none   => none
    | .bobj b _ => some b
    | _         => none
  match tp with
  | none    => .error s!"super:{c}.{m}:receiver"
  | some tp =>
    match ctx.mro tp with
    | none   => .error s!"mro:unknown-class:{tp}"
    | some l =>
      match l.dropWhile (· != c) with
      | _ :: rest =>
        match ctx.mroWalk m rest with
        | .found q => .ok q
        | .absent  => .error s!"super:{c}.{m}:absent"
        | .hole l  => .error l
      | [] => .error s!"super:{c}:not-in-mro-of:{tp}"

/-! ### Bare names under Python's rules

A bare name is a local (or a closure's captured binding), else a module global, else a
builtin. Legacy resolution consulted the **function table by suffix** first, so an
unbound `f` reached any function whose qualified name ends in `.f` — a method of an
unrelated class, a nested function of another scope. Under `pyStrict` the table is
consulted only for names the exporter qualified (`file.py:<module>.f`), which it does
exactly when Joern resolved the callee; an identifier is looked up by Python's scoping. -/

/-- Is this a Python identifier (so the exporter left it unqualified)? -/
def isPyIdent (s : String) : Bool :=
  match s.toList with
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun c => c.isAlphanum || c == '_')
  | []      => false

/-- Does Python scoping, rather than the function table, decide this name? -/
def Ctx.scopedName (ctx : Ctx) (f : String) : Bool := ctx.pyStrict && isPyIdent f

/-- The module-global binding of a name, if the globals frame has one. -/
def Ctx.globalVal? (ctx : Ctx) (h : Heap) (x : String) : Option Val :=
  match h.get ctx.globals with
  | some g => match g.fields.find? (·.1 == x) with
              | some (_, v) => some v
              | none        => none
  | none   => none

/-- The function-table entry a call `f(…)` resolves to before any variable is consulted.
Under Python's rules an identifier never does: it is a variable. -/
def Ctx.resolveCallee (ctx : Ctx) (f : String) : Option Func :=
  if ctx.scopedName f then none else ctx.resolve f

/-- `resolveCallee` only ever answers what `resolve` answers. -/
theorem Ctx.resolve_of_resolveCallee {ctx : Ctx} {f : String} {fn : Func}
    (h : ctx.resolveCallee f = some fn) : ctx.resolve f = some fn := by
  unfold Ctx.resolveCallee at h
  split at h
  · simp at h
  · exact h

/-- The value a called name holds. Legacy: the local environment only (`unit` if
unbound). Under Python's rules: local, else module global, else `unit` — which sends the
call to the builtins. A global bound to the builtin of the *same* name
(`isinstance = __builtin.isinstance`, which module initialisers record) is that builtin,
so it is also `unit` here. -/
def Ctx.calleeVal (ctx : Ctx) (h : Heap) (ρ : Env) (f : String) : Val :=
  if ctx.scopedName f then
    match ρ.find? (·.1 == f) with
    | some (_, v) => v
    | none =>
      match ctx.globalVal? h f with
      | some (.fn g) =>
          if g == "__builtin." ++ f || g == "__builtin." ++ f ++ "<meta>" then .unit else .fn g
      | some v       => v
      | none         => .unit
  else ρ.get f

/-- A bare name that is neither local nor global. Legacy: any function of that suffix, or
`unit`. Under Python's rules the honest answer is a hole: CPython would find a builtin or
raise `NameError`, and Core can tell neither apart from a binding its globals frame did
not receive (a module initialiser that holed, an import it does not model). -/
def Ctx.unboundName (ctx : Ctx) (x : String) : Val ⊕ String :=
  if ctx.scopedName x then .inr s!"name:unbound:{x}" else
  match ctx.resolve x with
  | some _ => .inl (.fn x)
  | none   => .inl .unit

/-- Does this class define this method *itself*? Unlike `resolveMethod` there is no
free-function fallback, so a global `__eq__` cannot be mistaken for a class's own. -/
def Ctx.classDefines (ctx : Ctx) (cls meth : String) : Bool :=
  ctx.table.any (fun p => p.1.endsWith ("." ++ cls ++ "." ++ meth))

/-- The builtin base of a class, if the exporter recorded one. -/
def Ctx.builtinBase (ctx : Ctx) (cls : String) : Option BuiltinBase :=
  match ctx.builtinBases.find? (·.1 == cls) with
  | some (_, b) => some b
  | none        => none

/-! ### Function objects

A Python function is a heap object with a `__dict__`, which is why `wrapper.cache_clear = f`
is an ordinary attribute write and not a special form. `Val.fn` is a bare name with no
identity, so that write used to hole as `setField:<f>:non-object` -- the largest single block
of INCONCLUSIVE cases in the conformance run. `Val.ref` already carries the identity `is`
compares, so the heap needs nothing new: a function that has been written to becomes an
object of the reserved class below, carrying the function it was. -/

/-- Reserved class of a boxed function object. Not a name any source language can produce. -/
def funcObjCls : String := "<function>"

/-- Reserved field holding the boxed function. -/
def funcObjField : String := "__fn__"

/-- Whether a value is callable-as-a-function, and so may be boxed on attribute write. -/
def isFnVal : Val → Bool
  | .fn _     => true
  | .clos _ _ => true
  | _         => false

/-- Box a function value into a heap object so it can carry attributes. -/
def boxFn (h : Heap) (fv : Val) : Heap × Ref :=
  h.alloc { cls := funcObjCls, fields := [(funcObjField, fv)] }

/-- The function a boxed function object carries, if it is one. -/
def unboxFn (h : Heap) (addr : Ref) : Option Val :=
  match h.get addr with
  | some o => if o.cls == funcObjCls then o.fields.lookup funcObjField else none
  | none   => none

/-- Dunders a class with a builtin base may **not** override and still be a `Val.bobj`:
every one of them is an operation Core performs on the payload directly, so an override
would be silently bypassed. Order matters only for which label a class that overrides
several gets; `__init__` and `__eq__` come first so existing labels are unchanged. -/
def builtinBaseRefusedDunders : List String :=
  [ "__init__", "__eq__", "__new__", "__ne__", "__getitem__", "__len__", "__iter__"
  , "__contains__", "__bool__", "__getattribute__" ]

/-- Construct an instance of a class whose base is a builtin type: `X(iterable)` for
`class X(tuple)` / `class X(list)`, `X(d)` for `class X(dict)`, `X(s)` for
`class X(str)`, and `X()` for the empty instance.

Deliberately **refuses** a class that overrides any dunder in
`builtinBaseRefusedDunders`, rather than approximating it:

* its own `__init__`/`__new__` — Core would have to run it against a value that has no
  mutable attributes, so whatever it did would be lost;
* its own `__eq__`/`__ne__` — `Val.beq` compares `bobj`s by contents and has no dunder
  dispatch, so an overridden `__eq__` would be silently ignored;
* its own `__getitem__`, `__len__`, `__iter__`, `__contains__`, `__bool__` or
  `__getattribute__` — indexing, `len`, iteration, `in` and truthiness of a `bobj` go
  straight to the payload (`Val.unbuiltin`, `Val.iterable`, `Stdlib.elems`, `valIn`,
  `Val.truthy`), so an override would be bypassed exactly as `__eq__` would be.

That is precisely the silent-wrong outcome this representation is supposed to avoid, so
each is a hole instead (`alloc:builtin-base:<cls>:own-<dunder>`).

`__hash__` is **not** refused: Core's `dict` lookup is by `Val.beq` alone, which agrees
with CPython for every class that keeps Python's documented invariant `a == b →
hash(a) == hash(b)` (`_HashedTuple.__hash__` memoises `tuple.__hash__`, so it does).
A class that breaks the invariant gets the builtin's lookup, not its own — recorded as an
assumption in `docs/core-language.md`, not checked here. Arithmetic dunders (`__add__`,
`__radd__`, …) need no refusal: `applyBinop` has no `bobj` case, so `+` on one is
already `binop:+`, a hole. -/
def allocBuiltin (ctx : Ctx) (cls : String) (b : BuiltinBase) (vs : List Val) : EResult :=
  match builtinBaseRefusedDunders.find? (ctx.classDefines cls ·) with
  | some d => .hole s!"alloc:builtin-base:{cls}:own-{d}"
  | none =>
    match vs with
    | []  => .val (.bobj cls b.empty)
    | [v] =>
        match b, v.unbuiltin with
        | .tuple, w =>
            match Stdlib.elems w with
            | some es => .val (.bobj cls (.tuple es))
            | none    => .hole s!"alloc:builtin-base:{cls}:non-iterable"
        | .list,  w =>
            match Stdlib.elems w with
            | some es => .val (.bobj cls (.list es))
            | none    => .hole s!"alloc:builtin-base:{cls}:non-iterable"
        -- `dict(pairs)` and `str(x)` on a non-string need `repr`/pair-unpacking that
        -- Core does not model, so only the identity coercions are accepted.
        | .dict,  .dict kvs => .val (.bobj cls (.dict kvs))
        | .dict,  _         => .hole s!"alloc:builtin-base:{cls}:dict-from-non-dict"
        | .str,   .str t    => .val (.bobj cls (.str t))
        | .str,   _         => .hole s!"alloc:builtin-base:{cls}:str-of-non-str"
    | _ => .hole s!"alloc:builtin-base:{cls}:multiple-args"

/-- `len(A((0,)))` is `1` in CPython for `class A(tuple)`: `len` of a builtin-based
instance is `len` of its payload. Done here, at the call site, rather than as a `bobj`
case in `Stdlib.builtinCore`, because a case there defeats the branch enumeration in
`Stdlib.builtin_heap_unchanged` (STRATEGY.md §35). Faithful because `allocBuiltin`
refuses any class that overrides `__len__` (`builtinBaseRefusedDunders`), so the
builtin's `len` is the one CPython would call. Every other builtin sees its arguments
unchanged: the ones that iterate already see through the base via `Stdlib.elems`, and
the rest must not be told a `bobj` is a plain container. -/
def builtinSeeThrough (f : String) (vs : List Val) : List Val :=
  if f == "len" then vs.map Val.unbuiltin else vs

/-- An unbound builtin method called through a variable: `add(self, other)` where
`add=tuple.__add__` is a default argument, which is how `cachetools`' `_HashedTuple`
concatenates without re-entering its own `__add__`.

Only `tuple.__add__` on two tuples (either possibly builtin-based) is answered, and the
result is a **plain** `tuple`, as in CPython: `tuple.__add__(A((0,)), (1,))` is `(0, 1)`
of type `tuple`, and the class is re-applied only by the caller's own `A(...)`. Every other
shape is `none` (a `call:<g>` hole): a non-tuple `other` makes CPython return
`NotImplemented` rather than raise, which Core has no value for. -/
def unboundBuiltinMethod (d : Dialect) (g : String) (vs : List Val) : Option EResult :=
  match d, g, vs with
  | .python, "tuple.__add__", [a, b] =>
      match a.unbuiltin, b.unbuiltin with
      | .tuple x, .tuple y => some (.val (.tuple (x ++ y)))
      | _,        _        => none
  | _, _, _ => none

/-! #### The legacy rules, as rewrites

A program without a class table (every corpus exported before §62, every non-Python one)
runs exactly the rules it always did. These equations say so per helper, as `simp` lemmas
conditional on `ctx.pyClasses = none`, so that proofs about such programs evaluate through
the new helpers without unfolding them. -/

@[simp] theorem Ctx.pyStrict_of_none {ctx : Ctx} (h : ctx.pyClasses = none) :
    ctx.pyStrict = false := by simp [Ctx.pyStrict, h]

@[simp] theorem Ctx.scopedName_of_none {ctx : Ctx} {f : String} (h : ctx.pyClasses = none) :
    ctx.scopedName f = false := by simp [Ctx.scopedName, h]

@[simp] theorem Ctx.resolveCallee_of_none {ctx : Ctx} {f : String} (h : ctx.pyClasses = none) :
    ctx.resolveCallee f = ctx.resolve f := by simp [Ctx.resolveCallee, h]

@[simp] theorem Ctx.calleeVal_of_none {ctx : Ctx} {hp : Heap} {ρ : Env} {f : String}
    (h : ctx.pyClasses = none) : ctx.calleeVal hp ρ f = ρ.get f := by
  simp [Ctx.calleeVal, h]

@[simp] theorem Ctx.unboundName_of_none {ctx : Ctx} {x : String} (h : ctx.pyClasses = none) :
    ctx.unboundName x = (match ctx.resolve x with
                         | some _ => .inl (.fn x)
                         | none   => .inl .unit) := by
  simp [Ctx.unboundName, h]

@[simp] theorem Ctx.makeSuper_of_none {ctx : Ctx} {f : String} {vs : List Val}
    (h : ctx.pyClasses = none) : ctx.makeSuper f vs = none := by
  simp [Ctx.makeSuper, h]

theorem Ctx.resolveMethod_of_none {ctx : Ctx} {c m : String}
    (h : ctx.pyClasses = none) : ctx.resolveMethod c m = ctx.resolveMethodLegacy c m := by
  simp [Ctx.resolveMethod, h]

theorem Ctx.classResponds_of_none {ctx : Ctx} {c m : String}
    (h : ctx.pyClasses = none) :
    ctx.classResponds c m = ctx.table.any (fun p => p.1.endsWith ("." ++ c ++ "." ++ m)) := by
  simp [Ctx.classResponds, h]

/-- Calling a builtin held as a VALUE (`fn = len; fn(x)`). Module initialisers bind the
builtins a module names (`len = __builtin.len`), so under Python's rules a name read as a
value is `Val.fn "__builtin.len"`; calling that is calling `len`. Legacy programs never
hold such a value through this path and keep their `call:` hole. -/
def Ctx.builtinOfValue (ctx : Ctx) (h : Heap) (g : String) (vs : List Val) :
    Option (Heap × EResult) :=
  if ctx.pyStrict && g.startsWith "__builtin." then
    let b0 := (g.drop "__builtin.".length).toString
    let b  := if b0.endsWith "<meta>" then b0.dropRight "<meta>".length else b0
    -- Exactly what a call of `b` by name does (the `Expr.call` fallthrough): boxed
    -- containers are seen through only where that is exact, and a fresh container a
    -- builtin builds is boxed.
    if builtinRefused h b vs then some (h, .hole s!"call:{b}:boxed-key") else
    match Stdlib.builtin ctx.dialect h b (builtinSeeThrough b (builtinArgs h b vs)) with
    | some (h₂, .val v) =>
        if ctx.dialect.isPython && freshBuiltins.contains b then
          let (h₃, v') := h₂.boxFresh v
          some (h₃, .val v')
        else some (h₂, .val v)
    | r => r
  else none

@[simp] theorem Ctx.builtinOfValue_of_none {ctx : Ctx} {h : Heap} {g : String} {vs : List Val}
    (hn : ctx.pyClasses = none) : ctx.builtinOfValue h g vs = none := by
  simp [Ctx.builtinOfValue, hn]

mutual

/-- Evaluate an expression, threading the heap. -/
def evalExpr (ctx : Ctx) : Nat → Heap → Env → Expr → Heap × EResult
  | 0,   h, _, _ => (h, .outOfFuel)
  | _+1, h, _, .lit (.int i)  => (h, .val (.int i))
  | _+1, h, _, .lit (.str s)  => (h, .val (.str s))
  | _+1, h, _, .lit (.bool b) => (h, .val (.bool b))
  | _+1, h, _, .lit (.float f) => (h, .val (.float f))
  | _+1, h, _, .lit .unit     => (h, .val .unit)
  | _+1, h, ρ, .name x        =>
      match ρ.find? (·.1 == x) with
      | some (_, v) => (h, .val v)
      | none        =>
        -- Item 5: a bare name that is not a local may still be a module-level function.
        -- Resolving it to a function value is what lets higher-order code (decorators,
        -- callbacks) be translated instead of holed.
        -- Under Python's rules (`Ctx.pyStrict`) a name bound nowhere is a hole rather
        -- than a same-suffix function: `Ctx.unboundName`.
        match h.get ctx.globals with
        | some g =>
          match g.fields.find? (·.1 == x) with
          | some (_, v) => (h, .val v)
          | none        => match ctx.unboundName x with
                           | .inl v => (h, .val v)
                           | .inr l => (h, .hole l)
        | none => match ctx.unboundName x with
                  | .inl v => (h, .val v)
                  | .inr l => (h, .hole l)
  | _+1, h, _, .fnref f       => (h, .val (.fn f))
  | _+1, h, ρ, .closure f     => (h, .val (.clos f ρ))
  | _+1, h, ρ, .classClosure c => (h, .val (.clsClos c ρ))
  | _+1, h, _, .hole l        => (h, .hole l)
  -- The three argument forms are only meaningful inside a call's argument list, where
  -- `evalList` intercepts them before `evalExpr` is ever reached. Anywhere else they have
  -- no value, and saying so is the honest answer.
  | _+1, h, _, .starred _     => (h, .hole "op:starred-outside-call")
  | _+1, h, _, .kwargE _ _    => (h, .hole "op:starred-outside-call")
  | _+1, h, _, .dstarred _    => (h, .hole "op:starred-outside-call")
  | n+1, h, ρ, .unop op a =>
      match evalExpr ctx n h ρ a with
      -- Through the heap: `not xs` on a boxed empty list is `True`.
      | (h₁, .val v) => (h₁, applyUnop ctx.dialect op (h₁.view v))
      | (h₁, r)      => (h₁, r)
  | n+1, h, ρ, .binop op a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val x) =>
        -- `&&` and `||` must NOT evaluate their right operand when the left already
        -- decides the answer. Eager evaluation was a genuine soundness bug, not a
        -- conservative approximation: `scripts/differential.py` caught
        -- `safemod(-11, 0)` returning 0 in CPython while Core raised ZeroDivisionError,
        -- because `b != 0 and a % b == 0` evaluated the division anyway.
        -- `and`/`or` are VALUE operators in Python and JavaScript: `a and b` is `a`
        -- when `a` is falsy and `b` otherwise, so `pick(0, 5)` is `5`, not `True`.
        -- Returning a bool was wrong for every Python program that uses them in
        -- value position; it survived because cachetools only uses them in
        -- conditions, where truthiness makes the two indistinguishable.
        -- C is the opposite: `&&`/`||` genuinely yield 0/1.
        if op == "&&" && !(h₁.view x).truthy then
          (h₁, .val (if ctx.dialect.boolOpsAreValues then x else .bool false))
        else if op == "||" && (h₁.view x).truthy then
          (h₁, .val (if ctx.dialect.boolOpsAreValues then x else .bool true))
        else
          match evalExpr ctx n h₁ ρ b with
          | (h₂, .val y) =>
            -- `==`/`!=` on a REFERENCE has to go through the heap: two distinct objects
            -- with equal contents are `==` in Python, and no structural compare of two
            -- refs can see that. Everything else keeps the heap-free path, which is the
            -- one `Refine.lean` needs reducible -- diverting here costs one call site
            -- instead of re-typing `applyBinop` and its 155 references.
            if binopNeedsHeap op x y then
              match ctx.dialect with
              -- JS `==` on objects is IDENTITY (`[1] == [1]` is `false`), never Python's
              -- value equality; `applyBinop`'s `jsEqE` decides it or holes.
              | .javascript => (h₂, applyBinop ctx.dialect op x y)
              | _ =>
              match Val.eqPy h₂ (Val.eqFuel h₂) x y with
              | some r => (h₂, .val (.bool (if op == "==" then r else !r)))
              | none   => (h₂, .outOfFuel)
            -- `and`/`or` yield an OPERAND, which must stay the object itself; every other
            -- operator sees a boxed container's contents (`xs + ys` concatenates them into a
            -- fresh value; the rest hole on containers exactly as before).
            else if op == "&&" || op == "||" then (h₂, applyBinop ctx.dialect op x y)
            else (h₂, applyBinop ctx.dialect op (h₂.view x) (h₂.view y))
          | (h₂, r)      => (h₂, r)
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .cond c t e =>
      match evalExpr ctx n h ρ c with
      | (h₁, .val v) => if (h₁.view v).truthy then evalExpr ctx n h₁ ρ t
                        else evalExpr ctx n h₁ ρ e
      | (h₁, r)      => (h₁, r)
  | n+1, h, ρ, .isOp neg a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val x) =>
        match evalExpr ctx n h₁ ρ b with
        | (h₂, .val y) =>
            -- `is` is reference identity. It used to fall back to a STRUCTURAL compare
            -- for immediates, which is a guess about interning: right for CPython's small
            -- ints, wrong for `[1] is [1]` (two allocations, `False`) and for large ints.
            -- `Val.identical` answers only where Core actually knows, and the rest becomes
            -- a hole rather than a plausible-looking wrong answer.
            match Val.identical x y with
            | some same => (h₂, .val (.bool (if neg then !same else same)))
            | none      => (h₂, .hole "is:unboxed-value-identity")
        | (h₂, r) => (h₂, r)
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .inOp neg a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val x) =>
        match evalExpr ctx n h₁ ρ b with
        | (h₂, .val c) =>
            match valInH ctx.dialect h₂ x c with
            | .val (.bool r) => (h₂, .val (.bool (if neg then !r else r)))
            | r              => (h₂, r)
        | (h₂, r) => (h₂, r)
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .index a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val c) =>
        match evalExpr ctx n h₁ ρ b with
        | (h₂, .val k) =>
          -- `A((0,))[0]` is `0` in CPython for `class A(tuple)`; a boxed container is
          -- read through the heap. A NEGATIVE index counts from the end under Python
          -- (`seqRead`); `Int.toNat` used to clamp it, so `xs[-1]` answered the FIRST
          -- element. Other dialects hole on it rather than guess.
          match (h₂.view c).unbuiltin, k with
          | .list vs, .int i  => (h₂, seqRead ctx.dialect vs i)
          | .tuple vs, .int i => (h₂, seqRead ctx.dialect vs i)
          | .dict kvs, key =>
              if ctx.dialect.isPython && h₂.unhashable key then (h₂, .exn (.str "TypeError"))
              else
              match kvs.find? (fun kv => Val.beq kv.1 key) with
              | some (_, v) => (h₂, .val v)
              | none        => (h₂, .exn (.str "KeyError"))
          | _, _ => (h₂, .hole "index:unsupported")
        | (h₂, r) => (h₂, r)
      | (h₁, r) => (h₁, r)
  -- `009-reduce-remaining-holes-4`: `Expr.strByte a b` -- read the byte at position
  -- `b` of string `a`, as an `Int`. See `Syntax.lean`'s own doc comment for why this
  -- is a separate constructor from `.index` rather than a new case on it. `a`'s own
  -- length is a valid index (C's own implicit null terminator, `0`); anything past it
  -- is undefined behaviour in C with no single correct answer, so it is a hole rather
  -- than a guess. A negative index is guarded explicitly: `Int.toNat` silently clamps
  -- a negative `Int` to `0`, which would otherwise alias `strByte s (-1)` to the FIRST
  -- character rather than reporting the honest problem.
  | n+1, h, ρ, .strByte a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val (.str s)) =>
        match evalExpr ctx n h₁ ρ b with
        | (h₂, .val (.int i)) =>
            let cs := s.toList
            if i < 0 then (h₂, .hole "strByte:negative-index")
            else if hh : i.toNat < cs.length then (h₂, .val (.int (Int.ofNat (cs[i.toNat]).toNat)))
            else if i.toNat == cs.length then (h₂, .val (.int 0))
            else (h₂, .hole "strByte:out-of-bounds")
        | (h₂, .val _) => (h₂, .hole "strByte:non-integer-index")
        | (h₂, r) => (h₂, r)
      | (h₁, .val _) => (h₁, .hole "strByte:non-string-receiver")
      | (h₁, r) => (h₁, r)
  -- `009-reduce-remaining-holes-4`: `Expr.strFrom a b` -- the substring of string `a`
  -- from position `b` onward. See `Syntax.lean`'s own doc comment: clamped like
  -- `List.drop` for a start past the string's own length (the empty string, not a
  -- hole), but a negative start is a hole -- the exporter never has a genuine reason
  -- to produce one.
  | n+1, h, ρ, .strFrom a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val (.str s)) =>
        match evalExpr ctx n h₁ ρ b with
        | (h₂, .val (.int i)) =>
            if i < 0 then (h₂, .hole "strFrom:negative-index")
            else (h₂, .val (.str (String.ofList (s.toList.drop i.toNat))))
        | (h₂, .val _) => (h₂, .hole "strFrom:non-integer-index")
        | (h₂, r) => (h₂, r)
      | (h₁, .val _) => (h₁, .hole "strFrom:non-string-receiver")
      | (h₁, r) => (h₁, r)
  -- The C address model (`Address.lean`): strict, left then right, then the
  -- heap-reading, fuel-free `applyPtrOp`.
  | n+1, h, ρ, .ptrOp op esz a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val x) =>
        match evalExpr ctx n h₁ ρ b with
        | (h₂, .val y) => (h₂, applyPtrOp h₂ op esz x y)
        | (h₂, r)      => (h₂, r)
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .field a f =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val (.ref r)) =>
        match h₁.get r with
        | some o =>
          match o.fields.find? (·.1 == f) with
          | some (_, v) => (h₁, .val v)
          | none        => match o.captured.find? (·.1 == f) with
                           | some (_, v) => (h₁, .val v)
                           -- A **module object** — the exporter's representation of an
                           -- imported module, marked by a class name beginning `<module>`
                           -- that no `class` statement in any language can spell — carries
                           -- exactly its top-level functions, classes and submodules. Its
                           -- module-level *data* is not a field, because Core's single
                           -- globals frame is not per-module and the value would have to
                           -- be captured before the module body computed it. Answering
                           -- `unit` for such an attribute is the silent wrong answer;
                           -- naming the miss is the honest one. Ordinary objects keep the
                           -- documented `unit` behaviour, so no existing corpus changes.
                           | none        =>
                             if o.cls.startsWith "<module>" then
                               (h₁, .hole s!"module-attr:{f}")
                             -- A boxed list or dict has no instance attributes (its fields
                             -- are always empty: it is allocated with none and
                             -- `Stmt.setField` refuses it), so an attribute read always lands
                             -- here. CPython raises `AttributeError`; `unit` would be a silent
                             -- wrong answer, so it is a hole.
                             else if ctx.dialect.isPython && (o.payload).toVal.isSome then
                               (h₁, .hole s!"field:{f}:builtin-container")
                             else (h₁, .val .unit)
        | none => (h₁, .val .unit)
      -- A C aggregate initializer is a `Val.dict` keyed by field name (see
      -- `Dialect.fieldsOnDicts`), so `alg.cra_priority` is a lookup in it. A *missing*
      -- key is a hole rather than `unit`: in C every field of a struct exists, so a name
      -- the initializer does not mention means the exporter and the semantics disagree
      -- about the shape, and inventing `unit` would hide that.
      | (h₁, .val (.dict kvs)) =>
          if ctx.dialect.fieldsOnDicts then
            match kvs.find? (fun kv => Val.beq kv.1 (.str f)) with
            | some (_, v) => (h₁, .val v)
            | none        => (h₁, .hole s!"field:{f}:absent-from-aggregate")
          else (h₁, .hole s!"field:{f}:non-object")
      | (h₁, .val _)        => (h₁, .hole s!"field:{f}:non-object")
      | (h₁, r)             => (h₁, r)
  -- `[*a, b]` and `(*a, b)` splice, exactly as in a call. `{**d}` has no display form
  -- here (a dict display is `dictE`), so a keyword group in a list/tuple literal is a
  -- shape we do not model and it says so.
  -- `docs/boxed-containers.md` step 3: a Python list/dict display is a fresh object.
  -- A dict display's pairs are stored the way repeated `d[k] = v` would store them, so a
  -- repeated key keeps its first position and its last value, and an unhashable key is
  -- CPython's `TypeError`.
  | n+1, h, ρ, .boxContainer e =>
      -- Only Python has boxed containers; the exporter emits this node for `.py` only, and
      -- refusing it elsewhere keeps "a payload object exists" a Python-only fact.
      if !ctx.dialect.isPython then (h, .hole "boxContainer:non-python") else
      match evalExpr ctx n h ρ e with
      | (h₁, .val (.list vs)) =>
          let (h₂, r) := h₁.alloc { cls := "list", fields := [], payload := .list vs }
          (h₂, .val (.ref r))
      | (h₁, .val (.dict kvs)) =>
          if kvs.any (fun kv => h₁.unhashable kv.1) then (h₁, .exn (.str "TypeError"))
          else
          let ps := kvs.foldl (fun acc kv => dictStore acc kv.1 kv.2) []
          let (h₂, r) := h₁.alloc { cls := "dict", fields := [], payload := .dict ps }
          (h₂, .val (.ref r))
      | (h₁, .val _) => (h₁, .hole "boxContainer:non-container")
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .listE es =>
      match evalList ctx n h ρ es with
      | (h₁, .inr (vs, []))  => (h₁, .val (.list vs))
      | (h₁, .inr (_,  _))   => (h₁, .hole "op:keyword-in-literal")
      | (h₁, .inl r)         => (h₁, r)
  | n+1, h, ρ, .tupleE es =>
      match evalList ctx n h ρ es with
      | (h₁, .inr (vs, []))  => (h₁, .val (.tuple vs))
      | (h₁, .inr (_,  _))   => (h₁, .hole "op:keyword-in-literal")
      | (h₁, .inl r)         => (h₁, r)
  | n+1, h, ρ, .dictE kvs =>
      match evalPairs ctx n h ρ kvs with
      | (h₁, .inr ps) => (h₁, .val (.dict ps))
      | (h₁, .inl r)  => (h₁, r)
  | n+1, h, ρ, .call f args =>
      match evalList ctx n h ρ args with
      | (h₁, .inl r)  => (h₁, r)
      | (h₁, .inr (vs, kws)) =>
        -- A name bound in the environment to a CLOSURE is that closure, before any
        -- function of the same (suffix) name in the table: Python resolves `inc()` in
        -- `def outer(): n = 0; def inc(): nonlocal n; ...; inc()` to the local variable
        -- `inc`, and the exporter, seeing Joern resolve the callee to
        -- `...outer.inc`, would otherwise reach that `Func` through `applyFunc` with NO
        -- captured environment -- every captured read unbound, and every write through a
        -- `nonlocal` cell a hole. Only `.clos` values take this path: a plain `.fn` held
        -- in a variable keeps the existing resolution order, so no closure-free program
        -- changes meaning.
        --
        -- Under Python's rules (`Ctx.pyStrict`) an unqualified name is a VARIABLE, full
        -- stop: `calleeVal` is the local, else the module global, and `resolveCallee`
        -- never consults the function table for it -- so a local `f` holding a function
        -- value is that value, and an unbound `f` goes to the builtins, never to some
        -- `...Cls.f` that happens to share the suffix.
        match (ctx.calleeVal h₁ ρ f).closParts? with
        | some (g, cap) =>
          match ctx.resolve g with
          | some fn => applyClosure ctx n h₁ fn cap vs kws
          | none    => (h₁, .hole s!"call:{g}")
        | none =>
        match ctx.resolveCallee f with
        | some fn => applyFunc ctx n h₁ fn none vs kws
        | none    =>
          -- Not a statically known function: it may be a function value or closure held
          -- in a variable (`f = g; f(x)`, decorators, callbacks).
          match ctx.calleeVal h₁ ρ f with
          | .fn g      => match ctx.resolve g with
                          | some fn =>
                            -- An unbound method reached through a VARIABLE -- a decorator's
                            -- wrapped function, a callback, `cache_getitem = Cache.__getitem__`
                            -- -- receives its receiver as the first POSITIONAL argument. That
                            -- is what `self` is in Python; the receiver is only implicit at a
                            -- `.`-call. `applyFunc` binds the receiver separately, so the head
                            -- has to be split off here, or it lands on `self`'s successor and
                            -- the call reports a spurious arity `TypeError`.
                            if fn.isMethod && fn.vararg.isNone
                               && vs.length == fn.params.length + 1 then
                              applyFunc ctx n h₁ fn (some (vs.headD .unit)) vs.tail kws
                            else applyFunc ctx n h₁ fn none vs kws
                          | none    =>
                            -- `add=tuple.__add__` held in a variable (`_HashedTuple`).
                            match (if kws.isEmpty then unboundBuiltinMethod ctx.dialect g vs
                                   else none) with
                            | some r => (h₁, r)
                            | none   =>
                            match (if kws.isEmpty then ctx.builtinOfValue h₁ g vs
                                   else none) with
                            | some (h₂, r) => (h₂, r)
                            | none         => (h₁, .hole s!"call:{g}")
          | .clos g cap => match ctx.resolve g with
                          | some fn => applyClosure ctx n h₁ fn cap vs kws
                          | none    => (h₁, .hole s!"call:{g}")
          | .ref addr  =>
            -- A function that has had an attribute written to it is now a boxed function
            -- object. Calling it calls what it carries; anything else on the heap is not
            -- callable and says so rather than guessing.
            match unboxFn h₁ addr with
            | some (.fn g)      => match ctx.resolve g with
                                   | some fn => applyFunc ctx n h₁ fn none vs kws
                                   | none    => (h₁, .hole s!"call:{g}")
            | some (.clos g cap) => match ctx.resolve g with
                                    | some fn => applyClosure ctx n h₁ fn cap vs kws
                                    | none    => (h₁, .hole s!"call:{g}")
            | _ => (h₁, .hole s!"call:{f}:not-callable")
          | _          =>
            -- Modelled stdlib is consulted LAST, so a user function of the same name
            -- always wins. `builtin` returns `none` for anything it cannot model
            -- faithfully, which falls through to a visible hole.
            -- `Stdlib.builtin` takes positional arguments only: a keyword argument to a
            -- builtin is *not* passed silently, it is a named hole.
            if kws.isEmpty then
              match ctx.makeSuper f vs with
              | some v => (h₁, .val v)
              | none   =>
              -- A boxed container is seen through the heap only by the builtins for which
              -- that is exact (`Boxed.builtinArgs`); a fresh container a builtin builds is
              -- itself boxed under Python, because in CPython it is a new object.
              if builtinRefused h₁ f vs then (h₁, .hole s!"call:{f}:boxed-key")
              else
              match Stdlib.builtin ctx.dialect h₁ f (builtinSeeThrough f (builtinArgs h₁ f vs)) with
              | some (h₂, .val v) =>
                  if ctx.dialect.isPython && freshBuiltins.contains f then
                    let (h₃, v') := h₂.boxFresh v
                    (h₃, .val v')
                  else (h₂, .val v)
              | some (h₂, r) => (h₂, r)
              | none         => (h₁, .hole s!"call:{f}")
            else (h₁, .hole s!"call:{f}:keyword-to-builtin")
  | n+1, h, ρ, .mcall recv m args =>
      match evalExpr ctx n h ρ recv with
      | (h₁, .val (.ref r)) =>
        match evalList ctx n h₁ ρ args with
        | (h₂, .inl e)  => (h₂, e)
        | (h₂, .inr (vs, kws)) =>
          match h₂.get r with
          | none   => (h₂, .hole "mcall:dangling-ref")
          -- A boxed list/dict: its builtin methods, on the payload, written back to the SAME
          -- reference. Checked BEFORE `resolveMethod`, whose free-function fallback would
          -- otherwise let a global `append` answer `xs.append(1)`.
          | some o =>
            match o.payload with
            | .list ps =>
                if kws.isEmpty then boxedMethod ctx.dialect h₂ r (.list ps) m vs
                else (h₂, .hole s!"mcall:{m}:keyword-to-builtin")
            | .dict ps =>
                if kws.isEmpty then boxedMethod ctx.dialect h₂ r (.dict ps) m vs
                else (h₂, .hole s!"mcall:{m}:keyword-to-builtin")
            | _ =>
            match ctx.resolveMethodOn o m with
            | none    =>
              -- `keys.hashkey(x)` on a **module object**. A module has no methods, so
              -- `resolveMethod` finds nothing; what it has is a *field* holding a
              -- function value, and a module-level function takes no receiver. Calling
              -- it with `self` bound would shift every argument by one, so the receiver
              -- is dropped — which is exactly what CPython does for an attribute that is
              -- a plain function rather than a class attribute.
              --
              -- Restricted to module objects on purpose. The same rule is *also* correct
              -- for an ordinary instance attribute holding a function (`self.cb(x)` does
              -- not pass `self` in CPython), and today that is the hole `mcall:C.cb`. But
              -- that is a claim about every class in every corpus, and it is not what
              -- this change is about; it stays a hole until it is measured on its own.
              if o.cls.startsWith "<module>" then
                match o.fields.find? (·.1 == m) with
                | some (_, .fn g)      =>
                    match ctx.resolve g with
                    | some fn => applyFunc ctx n h₂ fn none vs kws
                    | none    => (h₂, .hole s!"call:{g}")
                | some (_, .clos g cap) =>
                    match ctx.resolve g with
                    | some fn => applyClosure ctx n h₂ fn cap vs kws
                    | none    => (h₂, .hole s!"call:{g}")
                | some _  => (h₂, .hole s!"module-call:{m}:not-a-function")
                | none    => (h₂, .hole s!"module-attr:{m}")
              else (h₂, .hole s!"mcall:{o.cls}.{m}")
            | some fn =>
              if o.captured.isEmpty then applyFunc ctx n h₂ fn (some (.ref r)) vs kws
              else applyClosure ctx n h₂ fn (("self", .ref r) :: o.captured) vs kws
      | (h₁, .val (.fn g)) =>
        match evalList ctx n h₁ ρ args with
        | (h₂, .inl e)  => (h₂, e)
        | (h₂, .inr (vs, kws)) =>
          -- `Cache.__init__(self, maxsize, getsizeof)`: an UNBOUND method reached through
          -- the CLASS, which is how every subclass in cachetools calls its base
          -- constructor. Python passes the receiver as an ordinary first positional here;
          -- `applyFunc` binds receivers separately, so it has to be split off. Same rule
          -- as the `.fn` case in `Expr.call`, and it was worth six functions -- every
          -- `__init__` in the corpus was `mcall:__init__:non-object`.
          --
          -- The class value's name is the exporter's `<meta>` marker on the qualified
          -- name; `resolveMethod` wants the short class name, which is its last dotted
          -- segment (the FILE part contains dots, so this cannot split on the whole name).
          let short := classNameOfValue g
          -- `classDefines`, NOT `resolveMethod`: the latter falls back to any free
          -- function of that name, which for an opaque external module (`time.monotonic`)
          -- would invent a method out of an unrelated global. A hole is the right answer
          -- there; a plausible wrong one is not.
          if ctx.classResponds short m then
            match ctx.resolveMethod short m with
            | some fn =>
                match vs with
                | recv :: rest => applyFunc ctx n h₂ fn (some recv) rest kws
                | []           => (h₂, .hole s!"mcall:{short}.{m}:no-receiver")
            | none => (h₂, .hole s!"mcall:{m}:non-object")
          else (h₂, .hole s!"mcall:{short}.{m}:not-a-class-method")
      | (h₁, .val (.bobj bcls pay)) =>
        match evalList ctx n h₁ ρ args with
        | (h₂, .inl e)  => (h₂, e)
        | (h₂, .inr (vs, kws)) =>
          -- Method dispatch on a builtin-based instance: the class's own methods first
          -- (`self` is bound to the whole instance, so `self` still compares as the
          -- builtin), then the builtin's own methods on the payload.
          if ctx.classDefines bcls m then
            match ctx.resolveMethod bcls m with
            | some fn => applyFunc ctx n h₂ fn (some (.bobj bcls pay)) vs kws
            | none    => (h₂, .hole s!"mcall:{bcls}.{m}")
          else if kws.isEmpty then
            match Stdlib.method ctx.dialect h₂ pay m vs with
            | some (h₃, .pure r)       => (h₃, r)
            | some (h₃, .mutating _ _) => (h₃, .hole s!"mcall:{m}:unboxed-container")
            | none                     => (h₂, .hole s!"mcall:{bcls}.{m}")
          -- `Stdlib.method` has no keyword-argument calling convention, so a keyword
          -- call on a builtin payload is refused rather than silently dropped — the
          -- silent-drop of nine keyword arguments is what the varargs work just fixed.
          else (h₂, .hole s!"mcall:{m}:keyword-to-builtin")
      | (h₁, .val recv) =>
        match evalList ctx n h₁ ρ args with
        | (h₂, .inl e)  => (h₂, e)
        | (h₂, .inr (vs, kws)) =>
          -- `super().m(…)`: the proxy built by `Ctx.makeSuper`. Keyword arguments are
          -- passed through, exactly as to any method.
          match superParts? recv with
          | some (c, s) =>
            match ctx.superTarget h₂ c s m with
            | .ok q    => match ctx.resolve q with
                          | some fn => applyFunc ctx n h₂ fn (some s) vs kws
                          | none    => (h₂, .hole s!"call:{q}")
            | .error l => (h₂, .hole l)
          | none =>
          if !kws.isEmpty then (h₂, .hole s!"mcall:{m}:keyword-to-builtin") else
          match methodRefusal h₂ recv m vs with
          | some l => (h₂, .hole l)
          | none =>
          if methodKeyError ctx.dialect h₂ recv m vs then (h₂, .exn (.str "TypeError")) else
          match Stdlib.method ctx.dialect h₂ recv m vs with
          | some (h₃, .pure r)       => (h₃, r)
          -- A mutating container method cannot be honoured while containers are values:
          -- writing back through the receiver *expression* updates a temporary, because
          -- the CPG has already desugared `self.d.pop(k)` into `t = self.d; t.pop(k)`.
          -- An honest hole until containers are boxed (see docs/boxed-containers.md).
          | some (h₃, .mutating _ _) => (h₃, .hole s!"mcall:{m}:unboxed-container")
          | none                     => (h₂, .hole s!"mcall:{m}:non-object")
      | (h₁, r)      => (h₁, r)
  -- `003-box-address-taken-locals`: unconditional, constructor-free allocation of a
  -- fresh single-field box. Evaluate the argument, allocate `{cls := "<local>",
  -- fields := [("v", value)]}`, and yield the resulting `Val.ref` -- no class lookup,
  -- no `__init__`, unlike `.alloc` just below.
  | n+1, h, ρ, .boxNew e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v) =>
        let (h₂, r) := h₁.alloc { cls := "<local>", fields := [("v", v)] }
        (h₂, .val (.ref r))
      | (h₁, r) => (h₁, r)
  -- `006-reduce-remaining-holes`, Story 5: `Expr.boxNew` generalised to N fields --
  -- evaluate every (key, value) pair left-to-right, allocate one fresh `Obj` from the
  -- whole list, and yield `Val.ref`. The producer is the unconditional per-function
  -- allocation prologue for every array/struct local the exporter's own scope
  -- boundary admits (research.md §5.3-§5.4); this is what closes the pre-existing
  -- §5.1 gap (a plain struct local that looked hole-free but silently depended on a
  -- `setField` special case that did not cover it) for every struct this admits.
  --
  -- Reuses `evalPairs` verbatim (each key an `Expr`, always a string literal at
  -- every site the exporter emits) rather than a parallel `String`-keyed evaluator:
  -- `evalPairs` is already proven fuel-monotone as part of `dictE`'s own machinery
  -- (`Autoform/FuelMono.lean`), so `boxFields` needs no separate proof obligation of
  -- its own -- only the fuel-free key-extraction step below is new.
  | n+1, h, ρ, .boxFields kvs =>
      match evalPairs ctx n h ρ kvs with
      | (h₁, .inr pairs) =>
        match pairs.foldr (fun kv acc => match kv.1, acc with
                | .str k, some rest => some ((k, kv.2) :: rest)
                | _,      _         => none) (some []) with
        | some fields =>
          let (h₂, r) := h₁.alloc { cls := "<local>", fields := fields }
          (h₂, .val (.ref r))
        | none => (h₁, .hole "boxFields:non-string-key")
      | (h₁, .inl res) => (h₁, res)
  -- `010-reach-90pct-hole-free`: `Expr.boxArray` -- allocation of a fresh `Obj`
  -- whose field count is a RUNTIME value. Evaluate the length expression ONCE (the
  -- same single recursive `evalExpr` call `boxNew` above makes for its own one
  -- sub-expression -- same fuel shape, same proof shape), then build the fields
  -- list with a plain, non-fuel-consuming Lean function (`List.range`), never
  -- touching `evalPairs`/per-element `Expr` evaluation at all: every field starts
  -- `.unit`, so there is nothing to evaluate per element, only to COUNT. A negative
  -- length is a hole, not a crash or a silently-empty allocation -- the exporter
  -- never has a genuine reason to produce one (a `malloc`-shaped byte count is
  -- never negative in well-defined C), so seeing one here means the length
  -- expression itself was mistranslated, worth surfacing rather than masking.
  | n+1, h, ρ, .boxArray e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val (.int len)) =>
        if len < 0 then (h₁, .hole "boxArray:negative-length")
        else
          -- The C address model: the block's elements are BYTES (the exporter emits
          -- `boxArray` only for a `malloc`-shaped byte count assigned to a `char`/`u8`
          -- pointer), recorded in-band as `$esz` so typed pointer arithmetic
          -- (`Expr.ptrOp`) can check its stride. No decimal key, so `Heap.extent` and
          -- every element read are unaffected.
          let fields := (List.range len.toNat).map (fun i => (toString i, Val.unit)) ++
                        [("$esz", Val.int 1)]
          let (h₂, r) := h₁.alloc { cls := "<local>", fields := fields }
          (h₂, .val (.ref r))
      | (h₁, .val _) => (h₁, .hole "boxArray:non-int-length")
      | (h₁, r) => (h₁, r)
  -- `006-reduce-remaining-holes`, Story 5: `&a[i]` once `a` is a boxed array --
  -- evaluate the receiver to `Val.ref r`, evaluate the index, produce
  -- `Val.iref r (.idx i)`. Anything else is a shape the exporter's own scope
  -- boundary should never have emitted this node for; named as a hole rather than
  -- risking a wrong answer, per this project's own discipline.
  | n+1, h, ρ, .irefIndex a i =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val (.ref r)) =>
        match evalExpr ctx n h₁ ρ i with
        | (h₂, .val (.int k)) => (h₂, .val (.iref r (.idx k)))
        | (h₂, .val _)        => (h₂, .hole "irefIndex:non-int-index")
        | (h₂, res)           => (h₂, res)
      | (h₁, .val _) => (h₁, .hole "irefIndex:non-object")
      | (h₁, res)    => (h₁, res)
  -- `006-reduce-remaining-holes`, Story 5: `&s.f` once `s` is a boxed struct --
  -- evaluate the receiver to `Val.ref r`, produce `Val.iref r (.fld f)`.
  | n+1, h, ρ, .irefField a f =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val (.ref r)) => (h₁, .val (.iref r (.fld f)))
      | (h₁, .val _)        => (h₁, .hole "irefField:non-object")
      | (h₁, res)           => (h₁, res)
  -- `006-reduce-remaining-holes`, Story 5: `*p`, `p` an interior-pointer VALUE --
  -- requires the operand to evaluate to `Val.iref r sel` and delegates,
  -- unconditionally, to the unchanged `Heap.getField` -- no `Heap`-level change.
  | n+1, h, ρ, .derefIref a =>
      match evalExpr ctx n h ρ a with
      -- The C address model: an element read outside the array (one past the end
      -- included) is undefined behaviour, a hole -- it used to read the absent key as
      -- `.unit`, a value C never produced. Member selectors are unchanged.
      | (h₁, .val (.iref r sel)) =>
          match sel with
          | .idx i => if h₁.idxPos r i == .inside then (h₁, .val (h₁.getField r sel.key))
                      else (h₁, .hole "ub:ptr-deref-out-of-bounds")
          | .fld _ => (h₁, .val (h₁.getField r sel.key))
      | (h₁, .val _)             => (h₁, .hole "derefIref:non-iref")
      | (h₁, res)                => (h₁, res)
  | n+1, h, ρ, .alloc cls args =>
      match evalList ctx n h ρ args with
      | (h₁, .inl r)  => (h₁, r)
      | (h₁, .inr (vs, kws)) =>
        match ctx.builtinBase cls with
        -- `class X(tuple)` and friends: the instance IS the builtin, not an opaque
        -- reference. See `Val.bobj`.
        | some b => (h₁, allocBuiltin ctx cls b (vs.map h₁.view))
        | none =>
        -- A class defined inside a function is a *value*; instances carry the bindings it
        -- captured, so its methods can read the enclosing scope.
        let cap := match ρ.get cls with
                   | .clsClos _ c => c
                   | _            => []
        let (h₂, r) := h₁.alloc { cls := cls, fields := [], captured := cap }
        match ctx.resolveMethod cls "__init__" with
        | none    => (h₂, .val (.ref r))
        | some fn =>
          match applyFunc ctx n h₂ fn (some (.ref r)) vs kws with
          | (h₃, .val _)  => (h₃, .val (.ref r))
          | (h₃, .hole l) => (h₃, .hole l)
          | (h₃, e)       => (h₃, e)

/-- Apply a resolved function, optionally with a receiver bound to `self`.

`kws` carries the keyword arguments — `[]` for every call that has none, which is every
call this interpreter could express before starred arguments existed. -/
def applyFunc (ctx : Ctx) : Nat → Heap → Func → Option Val → List Val →
    List (String × Val) → Heap × EResult
  | 0,   h, _,  _,     _,  _   => (h, .outOfFuel)
  | n+1, h, fn, self?, vs, kws =>
      let base : Env := match self? with
                        | some s => [("self", s)]
                        | none   => []
      let ρ := bindParams fn base vs kws
      if kwargsRejected fn kws || posRejected fn vs then (h, .exn (.str "TypeError")) else
      match execStmt ctx n h ρ (fn.guardedBody vs kws) with
      | (h₁, .ret v)    => (h₁, .val v)
      | (h₁, .normal _) => (h₁, .val .unit)
      | (h₁, .exn v)    => (h₁, .exn v)
      | (h₁, .hole l)   => (h₁, .hole l)
      | (h₁, .outOfFuel)=> (h₁, .outOfFuel)
      | (h₁, _)         => (h₁, .hole "call:stray-control-flow")

/-- Apply a closure: the captured bindings form the base environment, then parameters
shadow them.

Capture is by value. Reads of enclosing variables therefore work, which covers decorators
and factory functions. A `nonlocal` **write** needs the binding to be a shared mutable
cell, and the exporter makes it one: every variable some inner function declares
`nonlocal` is allocated by its owner as a heap cell (`Expr.boxNew`), so what is captured
by value is the cell's reference, and a write through it is seen by the owner and every
other closure (STRATEGY.md §58). -/
def applyClosure (ctx : Ctx) : Nat → Heap → Func → List (String × Val) → List Val →
    List (String × Val) → Heap × EResult
  | 0,   h, _,  _,   _,  _   => (h, .outOfFuel)
  | n+1, h, fn, cap, vs, kws =>
      let base : Env := cap
      let ρ : Env := bindParams fn base vs kws
      if kwargsRejected fn kws || posRejected fn vs then (h, .exn (.str "TypeError")) else
      match execStmt ctx n h ρ (fn.guardedBody vs kws) with
      | (h₁, .ret v)     => (h₁, .val v)
      | (h₁, .normal _)  => (h₁, .val .unit)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
      | (h₁, _)          => (h₁, .hole "call:stray-control-flow")

/-- Evaluate an argument list left to right, short-circuiting on the first non-value, and
return the **positional** values together with the **keyword** bindings.

This is the one place the three argument forms of `Expr` mean anything:

* `*e` splices `e`'s elements into the positional list. A non-iterable `e` raises
  `TypeError`, as in CPython (`f(*1)`).
* `k = e` appends one keyword binding.
* `**e` splices a `dict` into the keyword bindings. A non-`dict`, or a `dict` with a
  non-string key, raises `TypeError`, as in CPython.

Every other expression contributes exactly one positional value, so the `kws` component is
`[]` for every argument list that predates this change and the whole of the previous
behaviour is recovered by projecting on the first component. -/
def evalList (ctx : Ctx) : Nat → Heap → Env → List Expr →
    Heap × Sum EResult (List Val × List (String × Val))
  | 0,   h, _, _       => (h, .inl .outOfFuel)
  | _+1, h, _, []      => (h, .inr ([], []))
  | n+1, h, ρ, .starred e :: as =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v) =>
        match (h₁.view v).iterable with
        | none    => (h₁, .inl (.exn (.str "TypeError")))
        | some xs =>
          match evalList ctx n h₁ ρ as with
          | (h₂, .inr (vs, kws)) => (h₂, .inr (xs ++ vs, kws))
          | (h₂, .inl r)         => (h₂, .inl r)
      | (h₁, r) => (h₁, .inl r)
  | n+1, h, ρ, .kwargE k e :: as =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v) =>
        match evalList ctx n h₁ ρ as with
        | (h₂, .inr (vs, kws)) => (h₂, .inr (vs, (k, v) :: kws))
        | (h₂, .inl r)         => (h₂, .inl r)
      | (h₁, r) => (h₁, .inl r)
  | n+1, h, ρ, .dstarred e :: as =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v) =>
        match strKeyed (h₁.view v) with
        | none    => (h₁, .inl (.exn (.str "TypeError")))
        | some ks =>
          match evalList ctx n h₁ ρ as with
          | (h₂, .inr (vs, kws)) => (h₂, .inr (vs, ks ++ kws))
          | (h₂, .inl r)         => (h₂, .inl r)
      | (h₁, r) => (h₁, .inl r)
  | n+1, h, ρ, a :: as =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val v) =>
        match evalList ctx n h₁ ρ as with
        | (h₂, .inr (vs, kws)) => (h₂, .inr (v :: vs, kws))
        | (h₂, .inl r)         => (h₂, .inl r)
      | (h₁, r) => (h₁, .inl r)

/-- Evaluate a list of key/value expression pairs. -/
def evalPairs (ctx : Ctx) : Nat → Heap → Env → List (Expr × Expr) →
    Heap × Sum EResult (List (Val × Val))
  | 0,   h, _, _            => (h, .inl .outOfFuel)
  | _+1, h, _, []           => (h, .inr [])
  | n+1, h, ρ, (k, v) :: ps =>
      match evalExpr ctx n h ρ k with
      | (h₁, .val kv) =>
        match evalExpr ctx n h₁ ρ v with
        | (h₂, .val vv) =>
          match evalPairs ctx n h₂ ρ ps with
          | (h₃, .inr rest) => (h₃, .inr ((kv, vv) :: rest))
          | (h₃, .inl r)    => (h₃, .inl r)
        | (h₂, r) => (h₂, .inl r)
      | (h₁, r) => (h₁, .inl r)

/-- Execute a statement, threading the heap. -/
def execStmt (ctx : Ctx) : Nat → Heap → Env → Stmt → Heap × Ctl
  | 0,   h, _, _ => (h, .outOfFuel)
  | _+1, h, ρ, .skip   => (h, .normal ρ)
  | _+1, h, ρ, .brk    => (h, .brk ρ)
  | _+1, h, ρ, .cont   => (h, .cont ρ)
  | _+1, h, _, .hole l => (h, .hole l)
  | _+1, h, ρ, .del x  => (h, .normal (ρ.del x))
  -- `global x` records a marker; `assign` consults it so that `global x; x = 1` writes
  -- module scope rather than silently creating a local and losing the update.
  | _+1, h, ρ, .declGlobal x => (h, .normal (ρ.set ("<glob>" ++ x) (.bool true)))
  | n+1, h, ρ, .expr e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val _)     => (h₁, .normal ρ)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .setGlobal x e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v)     => (h₁.setField ctx.globals x v, .normal ρ)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .assign x e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v)     =>
          if (ρ.get ("<glob>" ++ x)).truthy then (h₁.setField ctx.globals x v, .normal ρ)
          else (h₁, .normal (ρ.set x v))
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .ret e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v)     => (h₁, .ret v)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .raise e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v)     => (h₁, .exn v)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .setField r f v =>
      match evalExpr ctx n h ρ r with
      | (h₁, .val (.ref addr)) =>
        -- CPython: `AttributeError: 'list' object has no attribute ...`. Not modelled as
        -- that exception (a `list` SUBCLASS would accept it), so a hole.
        if (h₁.payload addr).toVal.isSome then (h₁, .hole s!"setField:{f}:builtin-container")
        else
        match evalExpr ctx n h₁ ρ v with
        | (h₂, .val vv)    => (h₂.setField addr f vv, .normal ρ)
        | (h₂, .exn e)     => (h₂, .exn e)
        | (h₂, .hole l)    => (h₂, .hole l)
        | (h₂, .outOfFuel) => (h₂, .outOfFuel)
      | (h₁, .val fv) =>
        -- A function is a heap object in Python, so an attribute write to one is legal.
        -- It is only expressible here when the receiver is a NAME: boxing rebinds that
        -- name to the new object, and a function value reached any other way has nowhere
        -- to rebind, so it keeps holing. That is correct rather than convenient -- the
        -- alternative silently drops the mutation.
        match r with
        | .name x =>
          if isFnVal fv then
            let (h₂, addr) := boxFn h₁ fv
            match evalExpr ctx n h₂ ρ v with
            | (h₃, .val vv)    => (h₃.setField addr f vv, .normal (Env.set ρ x (.ref addr)))
            | (h₃, .exn e)     => (h₃, .exn e)
            | (h₃, .hole l)    => (h₃, .hole l)
            | (h₃, .outOfFuel) => (h₃, .outOfFuel)
          else (h₁, .hole s!"setField:{f}:non-object")
        | _ => (h₁, .hole s!"setField:{f}:non-object")
      | (h₁, .exn e) => (h₁, .exn e)
      | (h₁, .hole l) => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  -- `docs/boxed-containers.md` step 4. Only Python has boxed containers; every other
  -- dialect keeps the original hole, unevaluated, exactly as before.
  --
  -- CPython's order for `e[i] = v` is `v`, then `e`, then `i`. A boxed container is
  -- written with `Heap.setPayload` on the reference `e` evaluated to -- never through the
  -- expression `e`, which is what makes a write through one alias visible through every
  -- other. A plain object runs its class's own `__setitem__`; anything else is
  -- `valueSubscriptWrite`'s `TypeError` (immutable values) or hole (unboxed containers).
  | n+1, h, ρ, .setIndex e i v =>
      if !ctx.dialect.isPython then (h, .hole "setIndex:immutable-containers") else
      match evalExpr ctx n h ρ v with
      | (h₁, .val x) =>
        match evalExpr ctx n h₁ ρ e with
        | (h₂, .val c) =>
          match evalExpr ctx n h₂ ρ i with
          | (h₃, .val k) =>
            match c with
            | .ref r =>
              match h₃.get r with
              | none => (h₃, .hole "setIndex:dangling-ref")
              | some o =>
                match o.payload with
                | .none =>
                  if ctx.classResponds o.cls "__setitem__" then
                    match ctx.resolveMethod o.cls "__setitem__" with
                    | some fn =>
                      match (if o.captured.isEmpty
                             then applyFunc ctx n h₃ fn (some (.ref r)) [k, x] []
                             else applyClosure ctx n h₃ fn (("self", .ref r) :: o.captured)
                                    [k, x] []) with
                      | (h₄, .val _)     => (h₄, .normal ρ)
                      | (h₄, .exn ex)    => (h₄, .exn ex)
                      | (h₄, .hole l)    => (h₄, .hole l)
                      | (h₄, .outOfFuel) => (h₄, .outOfFuel)
                    | none => (h₃, .hole s!"setIndex:{o.cls}")
                  else (h₃, .hole s!"setIndex:{o.cls}:no-own-__setitem__")
                | p =>
                  match payloadStore h₃ p k x with
                  | .ok p'   => (h₃.setPayload r p', .normal ρ)
                  | .exn ex  => (h₃, .exn (.str ex))
                  | .hole l  => (h₃, .hole l)
            | c =>
              match valueSubscriptWrite ctx.dialect c "setIndex" with
              | .exn ex => (h₃, .exn ex)
              | .hole l => (h₃, .hole l)
              | _       => (h₃, .hole "setIndex:immutable-containers")
          | (h₃, .exn ex)    => (h₃, .exn ex)
          | (h₃, .hole l)    => (h₃, .hole l)
          | (h₃, .outOfFuel) => (h₃, .outOfFuel)
        | (h₂, .exn ex)    => (h₂, .exn ex)
        | (h₂, .hole l)    => (h₂, .hole l)
        | (h₂, .outOfFuel) => (h₂, .outOfFuel)
      | (h₁, .exn ex)    => (h₁, .exn ex)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  -- `del e[i]`: CPython evaluates `e`, then `i`. Mirrors `setIndex`.
  | n+1, h, ρ, .delIndex e i =>
      if !ctx.dialect.isPython then (h, .hole "op:delete-index") else
      match evalExpr ctx n h ρ e with
      | (h₁, .val c) =>
        match evalExpr ctx n h₁ ρ i with
        | (h₂, .val k) =>
          match c with
          | .ref r =>
            match h₂.get r with
            | none => (h₂, .hole "delIndex:dangling-ref")
            | some o =>
              match o.payload with
              | .none =>
                if ctx.classResponds o.cls "__delitem__" then
                  match ctx.resolveMethod o.cls "__delitem__" with
                  | some fn =>
                    match (if o.captured.isEmpty
                           then applyFunc ctx n h₂ fn (some (.ref r)) [k] []
                           else applyClosure ctx n h₂ fn (("self", .ref r) :: o.captured)
                                  [k] []) with
                    | (h₃, .val _)     => (h₃, .normal ρ)
                    | (h₃, .exn ex)    => (h₃, .exn ex)
                    | (h₃, .hole l)    => (h₃, .hole l)
                    | (h₃, .outOfFuel) => (h₃, .outOfFuel)
                  | none => (h₂, .hole s!"delIndex:{o.cls}")
                else (h₂, .hole s!"delIndex:{o.cls}:no-own-__delitem__")
              | p =>
                match payloadDelete h₂ p k with
                | .ok p'   => (h₂.setPayload r p', .normal ρ)
                | .exn ex  => (h₂, .exn (.str ex))
                | .hole l  => (h₂, .hole l)
          | c =>
            match valueSubscriptWrite ctx.dialect c "delIndex" with
            | .exn ex => (h₂, .exn ex)
            | .hole l => (h₂, .hole l)
            | _       => (h₂, .hole "delIndex:immutable-containers")
        | (h₂, .exn ex)    => (h₂, .exn ex)
        | (h₂, .hole l)    => (h₂, .hole l)
        | (h₂, .outOfFuel) => (h₂, .outOfFuel)
      | (h₁, .exn ex)    => (h₁, .exn ex)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  -- `006-reduce-remaining-holes`, Story 5: `*p = v`, `p` an interior-pointer VALUE --
  -- requires the pointer operand to evaluate to `Val.iref r sel` and delegates,
  -- unconditionally, to the unchanged `Heap.setField`.
  | n+1, h, ρ, .setDerefIref p v =>
      match evalExpr ctx n h ρ p with
      | (h₁, .val (.iref r sel)) =>
        match evalExpr ctx n h₁ ρ v with
        -- The C address model: a write outside the array is undefined behaviour --
        -- it used to ADD a key, silently growing the block (and breaking the
        -- contiguity `Heap.extent` relies on).
        | (h₂, .val vv)    =>
            match sel with
            | .idx i => if h₂.idxPos r i == .inside then (h₂.setField r sel.key vv, .normal ρ)
                        else (h₂, .hole "ub:ptr-store-out-of-bounds")
            | .fld _ => (h₂.setField r sel.key vv, .normal ρ)
        | (h₂, .exn e)     => (h₂, .exn e)
        | (h₂, .hole l)    => (h₂, .hole l)
        | (h₂, .outOfFuel) => (h₂, .outOfFuel)
      | (h₁, .val _)      => (h₁, .hole "setDerefIref:non-iref")
      | (h₁, .exn e)      => (h₁, .exn e)
      | (h₁, .hole l)     => (h₁, .hole l)
      | (h₁, .outOfFuel)  => (h₁, .outOfFuel)
  | n+1, h, ρ, .seq a b =>
      match execStmt ctx n h ρ a with
      | (h₁, .normal ρ') => execStmt ctx n h₁ ρ' b
      | (h₁, r)          => (h₁, r)
  | n+1, h, ρ, .ifte c t e =>
      match evalExpr ctx n h ρ c with
      | (h₁, .val v)     => if (h₁.view v).truthy then execStmt ctx n h₁ ρ t
                            else execStmt ctx n h₁ ρ e
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .tryFinally body fin =>
      match execStmt ctx n h ρ body with
      | (h₁, .normal ρ') => execStmt ctx n h₁ ρ' fin
      | (h₁, r) =>
          -- The finalizer runs on every path. If it exits abnormally it *discards* the
          -- body's pending outcome: `try: return 1 finally: return 2` returns 2.
          let ρ' := match r with
                    | .normal e | .brk e | .cont e => e
                    | _                            => ρ
          match execStmt ctx n h₁ ρ' fin with
          | (h₂, .normal _) => (h₂, r)
          | (h₂, r')        => (h₂, r')
  | n+1, h, ρ, .tryCatch body x handler =>
      match execStmt ctx n h ρ body with
      | (h₁, .exn v) => execStmt ctx n h₁ (ρ.set x v) handler
      | (h₁, r)      => (h₁, r)
  | n+1, h, ρ, .loop c body =>
      match evalExpr ctx n h ρ c with
      | (h₁, .val v) =>
          if (h₁.view v).truthy then
            match execStmt ctx n h₁ ρ body with
            | (h₂, .normal ρ') => execStmt ctx n h₂ ρ' (.loop c body)
            | (h₂, .cont ρ')   => execStmt ctx n h₂ ρ' (.loop c body)
            | (h₂, .brk ρ')    => (h₂, .normal ρ')
            | (h₂, r)          => (h₂, r)
          else (h₁, .normal ρ)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  -- `007-reduce-remaining-holes-2` US4: catches a `.brk` from its inner statement and
  -- converts it to `.normal`, exactly once (no re-execution, unlike `.loop`) --
  -- deliberately does NOT catch `.cont`, so a `continue` written directly in a
  -- `switch` case body keeps propagating to whatever REAL loop encloses the switch,
  -- unchanged. This is the one thing `.loop`/`.forIn` do not provide on their own.
  | n+1, h, ρ, .breakBlock body =>
      match execStmt ctx n h ρ body with
      | (h₁, .brk ρ') => (h₁, .normal ρ')
      | (h₁, r)       => (h₁, r)
  | n+1, h, ρ, .forIn x e body =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v) =>
        match (h₁.view v).iterable with
        | some vs =>
          match v with
          -- A boxed container is iterated over a SNAPSHOT, and the snapshot is only
          -- faithful if nothing wrote to the object meanwhile: CPython's list iterator
          -- would have seen the write, and its dict iterator raises `RuntimeError`. So a
          -- moved `version` turns the outcome into a hole rather than an answer.
          | .ref r =>
            let ver := h₁.version r
            match execFor ctx n h₁ ρ x vs body with
            | (h₂, .outOfFuel) => (h₂, .outOfFuel)
            | (h₂, c) =>
              if h₂.version r == ver then (h₂, c)
              else (h₂, .hole "forIn:container-mutated-during-iteration")
          | _ => execFor ctx n h₁ ρ x vs body
        | none    => (h₁, .hole "forIn:non-iterable")
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)

/-- Run a loop body once per element of an already-computed sequence. -/
def execFor (ctx : Ctx) : Nat → Heap → Env → String → List Val → Stmt → Heap × Ctl
  | 0,   h, ρ, _, _,       _    => (h, .outOfFuel)
  | _+1, h, ρ, _, [],      _    => (h, .normal ρ)
  | n+1, h, ρ, x, v :: vs, body =>
      match execStmt ctx n h (ρ.set x v) body with
      | (h₁, .normal ρ') => execFor ctx n h₁ ρ' x vs body
      | (h₁, .cont ρ')   => execFor ctx n h₁ ρ' x vs body
      | (h₁, .brk ρ')    => (h₁, .normal ρ')
      | (h₁, r)          => (h₁, r)

end

/-- A one-element argument list, when that argument is an ordinary one. Stated because a
*symbolic* expression cannot be dispatched on: `evalList` looks at the argument's syntax
before evaluating it, so knowing what `evalExpr` does to `e` is not by itself enough to
know what `evalList` does to `[e]`. -/
theorem evalList_singleton (ctx : Ctx) (n : Nat) (h : Heap) (ρ : Env) {e : Expr}
    (hp : e.plainArg = true) :
    evalList ctx (n+2) h ρ [e] =
      (match evalExpr ctx (n+1) h ρ e with
       | (h₁, .val v) => (h₁, .inr ([v], []))
       | (h₁, r)      => (h₁, .inl r)) := by
  cases e
  case starred _ => exact absurd hp (by simp [Expr.plainArg])
  case kwargE _ _ => exact absurd hp (by simp [Expr.plainArg])
  case dstarred _ => exact absurd hp (by simp [Expr.plainArg])
  all_goals rfl

/-- Run a named entry point against argument values, with **no** module-level state.

Deliberately unchanged: it starts from the empty heap, so `Heap.get ctx.globals` finds
nothing and a free name falls through to the function table. This is the right entry point
for a self-contained function, and keeping it stable keeps the refinement layer's
theorems meaningful. Use `runMain` when module-level bindings matter. -/
def runFunc (p : Program) (fuel : Nat) (name : String) (args : List Val) : EResult :=
  let ctx : Ctx := { dialect := p.dialect, table := p.table,
                     builtinBases := p.builtinBases,
                     pyClasses := p.pyClasses }
  match ctx.resolve name with
  | none    => .hole s!"entry:{name}"
  | some fn => (applyFunc ctx fuel [] fn none args []).2

/-- Run the module initializers and return the resulting heap plus the globals address.

Exposed separately from `runMain` so that a harness which builds its own heap (e.g. the
differential oracle, which materialises receiver objects) can start from an initialised
globals frame instead of the empty heap. Fresh objects must be allocated at indices from
`heap.length` onward. -/
def initGlobals (p : Program) (fuel : Nat) (inits : List Func) : Heap × Ref :=
  let (h₀, g) := Heap.alloc ([] : Heap) { cls := "<globals>", fields := [] }
  let ctx : Ctx := { dialect := p.dialect, table := p.table, globals := g,
                     builtinBases := p.builtinBases,
                     pyClasses := p.pyClasses }
  let rec go : Nat → Heap → List Func → Heap
    | 0,   h, _       => h
    | _+1, h, []      => h
    | n+1, h, f :: fs => go n (applyFunc ctx fuel h f none [] []).1 fs
  (go (inits.length + 1) h₀ inits, g)

/-- Run module initializers into a shared globals frame, then call an entry point.

Module-level bindings are mutable and outlive any single call, so they live in a heap
object rather than in `Env`. The transpiler emits one zero-argument `Func` per source
module (`moduleInits`); running them in order is what makes module constants, classes and
functions resolvable.

Initializer order is the caller's responsibility: the transpiler cannot recover a
cross-file dependency order from the CPG, so a module that reads another module's globals
must be listed after it. That is a real limitation, not a detail — it is recorded as an
open item rather than papered over with a guessed ordering. -/
def runMain (p : Program) (fuel : Nat) (inits : List Func) (name : String)
    (args : List Val) : EResult :=
  let (h₀, g) := Heap.alloc ([] : Heap) { cls := "<globals>", fields := [] }
  let ctx : Ctx := { dialect := p.dialect, table := p.table, globals := g,
                     builtinBases := p.builtinBases,
                     pyClasses := p.pyClasses }
  let rec runInits : Nat → Heap → List Func → Heap × Option String
    | 0,   h, _       => (h, some "initializers:outOfFuel")
    | _+1, h, []      => (h, none)
    | n+1, h, f :: fs =>
        match applyFunc ctx fuel h f none [] [] with
        | (h₁, .val _)     => runInits n h₁ fs
        | (h₁, .hole l)    => (h₁, some l)
        | (h₁, .exn _)     => runInits n h₁ fs   -- an initializer that raises still bound
                                                  -- whatever it bound before raising
        | (h₁, .outOfFuel) => (h₁, some "initializers:outOfFuel")
  match runInits (inits.length + 1) h₀ inits with
  | (_,  some l) => .hole l
  | (h₁, none)   =>
    match ctx.resolve name with
    | none    => .hole s!"entry:{name}"
    | some fn => (applyFunc ctx fuel h₁ fn none args []).2

/-! ## C and C++ pointers, end to end

The exporter now maps `p->f` to `Expr.field`, `p[i]` to `Expr.index`, C++ stack
construction to `Expr.alloc`, and `&x` on an aggregate to `x` itself. Each of those is a
*mapping* decision, and a mapping decision is exactly the kind that can be wrong while
every downstream theorem still passes: an `Expr.field` that resolved to nothing would
return `unit`, a program full of them would type-check, and the ledger would count it as
translated. So the mappings are checked here by running them.

`boxProg` is what the exporter emits for

    struct Box { int v; Box(int x) { this->v = x; } };
    static int bump(Box *p) { p->v = p->v + 1; return p->v; }
    int run() { Box b(41); return bump(&b); }

with every one of the new decisions visible in the term: the constructor is named
`__init__` (so `Expr.alloc` runs it), its body writes through `self` (not `this`),
`bump` reads and writes `p->v` as `Expr.field` / `Stmt.setField`, and `&b` is just `b`. -/
private def boxProg : Program :=
  { dialect := .cLike
  , funcs :=
    [ { name   := "ns.Box.__init__"
      , params := ["x"]
      , body   := .setField (.name "self") "v" (.name "x") }
    , { name   := "ns.bump"
      , params := ["p"]
      , body   := .seq (.setField (.name "p") "v"
                          (.binop "+" (.field (.name "p") "v") (.lit (.int 1))))
                       (.ret (.field (.name "p") "v")) }
    , { name   := "ns.run"
      , params := []
      , body   := .seq (.assign "b" (.alloc "Box" [.lit (.int 41)]))
                       (.ret (.call "ns.bump" [.name "b"])) }
      -- `static_cast<uint8_t>(300 + 44)` — a real narrowing, in a real program.
    , { name   := "ns.narrow"
      , params := []
      , body   := .ret (.unop "cast:u8" (.binop "+" (.lit (.int 300)) (.lit (.int 44)))) }
      -- `int a[3] = {7,8,9}; return a[1];` as Core spells an indexable value.
    , { name   := "ns.pick"
      , params := []
      , body   := .ret (.index (.listE [.lit (.int 7), .lit (.int 8), .lit (.int 9)])
                               (.lit (.int 1))) }
      -- The negative control: an object whose field was never written.
    , { name   := "ns.unset"
      , params := []
      , body   := .ret (.field (.alloc "Empty" []) "v") } ] }

/-! The whole chain works: `Box b(41)` allocates and runs the constructor, `&b` is `b`,
`p->v = p->v + 1` mutates *that* object, and the caller sees `42`.

`42` is the load-bearing number. `41` would mean the constructor ran but the write
through the pointer did not reach the same object; `unit` would mean the field read
missed; a hole would mean one of the four mappings is unreachable. Only a correct
pointer round-trip produces `42`.

These are pinned with `#guard_msgs`, not `rfl`: `runFunc` on a heap-allocating program
does not reduce by `whnf` (the `.alloc` case threads a heap through `applyFunc`), so
`rfl` cannot see the answer even though the evaluator computes it immediately.
`#guard_msgs` checks the evaluated result at build time and fails the build if it
changes, which is the property wanted here — and unlike `native_decide` it introduces no
axiom. -/
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 42) -/
#guard_msgs in #eval runFunc boxProg 200 "ns.run" []

/-- The cast narrows: `static_cast<uint8_t>(344)` is `88`, matching `cc`. This one does
reduce, so it is stated as a theorem as well. -/
example : runFunc boxProg 200 "ns.narrow" [] = .val (.int 88) := by rfl

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 88) -/
#guard_msgs in #eval runFunc boxProg 200 "ns.narrow" []

/-- Subscripting reads the element, not the container. -/
example : runFunc boxProg 200 "ns.pick" [] = .val (.int 8) := by rfl

/-! **The known hazard, stated rather than hidden.** `Expr.field` on an object that has
no such field returns `unit`, not a hole — see the `.field` case above. So a C++ class
whose constructor the exporter could not find translates to an object every one of whose
fields reads `unit`, and nothing downstream will say so.

That is why `emit` renames C++ constructors to `__init__` instead of leaving `Expr.alloc`
to allocate an empty object, and why `alloc:builtin-base:*` refuses construction it cannot
model. This check exists so the behaviour is a recorded fact with a test attached, and so
that changing it is a deliberate act rather than an accident. -/
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.unit) -/
#guard_msgs in #eval runFunc boxProg 200 "ns.unset" []


/-! ## Bitwise operators, `for`, and `goto`, checked against `cc`

Every number below was produced by compiling the same fragment with `cc -O0 -fwrapv` on
x86-64 and running it. They are pinned with `#guard_msgs`, which fails the build if the
semantics changes and — unlike `native_decide` — introduces no axiom.

These exist because "the label disappeared from the ledger" is not evidence. An `xor`
that returned `0`, an array initializer that evaluated to `unit`, or a `for` that ran zero
times would each remove a hole and prove nothing; only a checked *value* does. Where a
translation could plausibly have been done a wrong-but-plausible way, the wrong way is
included as a negative control and shown to disagree.
-/

section CEvidence

/-- The C constructs the exporter now translates, spelled in Core exactly as it spells
them.

`ns.forSum` is the interesting one. It is the translation of

    int i, s = 0;
    for (i = 0; i < 10; i++) { if (i % 3 == 0) continue; s += i; }
    return s * 100 + i;

under the rule that a `for`'s `continue` must run the **step**: each `continue` in the
body is emitted as `step; continue`. `cc` prints `s=27 i=10`, so the answer is `2710`.

`ns.forNaive` is the same loop under the *textbook* desugaring — `init; while (c) { body;
step }` with the `continue` left alone. It is the negative control, and it does not
terminate: the `continue` jumps back to the test without incrementing `i`. -/
private def cBits : Program :=
  { dialect := .cLike
  , funcs :=
    [ { name := "ns.xor",   params := [],
        body := .ret (.binop "^" (.lit (.int 0x5A)) (.lit (.int 0x3C))) }
    , { name := "ns.and",   params := [],
        body := .ret (.binop "&" (.lit (.int (-1))) (.lit (.int 255))) }
    , { name := "ns.or",    params := [],
        body := .ret (.binop "|" (.lit (.int 0xF0)) (.lit (.int 0x0F))) }
    , { name := "ns.bnot",  params := [],
        body := .ret (.unop "~" (.lit (.int 0x5A))) }
    , { name := "ns.shl",   params := [],
        body := .ret (.binop "<<" (.lit (.int 1)) (.lit (.int 31))) }
    , { name := "ns.sar",   params := [],
        body := .ret (.binop ">>" (.lit (.int (-8))) (.lit (.int 1))) }
    , { name := "ns.sarNeg", params := [],
        body := .ret (.binop ">>" (.lit (.int (-1))) (.lit (.int 4))) }
      -- `unsigned u = 0x80000000u; u >> 31` — the *logical* shift, which the exporter
      -- emits as `>>>` because the left operand's static type is unsigned.
    , { name := "ns.shrU",  params := [],
        body := .ret (.binop ">>>" (.lit (.int 0x80000000)) (.lit (.int 31))) }
      -- The same bits arrived at by wrapping arithmetic, which is how the value actually
      -- shows up when it is computed rather than written down.
    , { name := "ns.shrUw", params := [],
        body := .ret (.binop ">>>" (.binop "<<" (.lit (.int 1)) (.lit (.int 31)))
                                   (.lit (.int 31))) }
    , { name := "ns.shrU4", params := [],
        body := .ret (.binop ">>>" (.lit (.int 0xF0000000)) (.lit (.int 4))) }
      -- The negative control for the `>>` / `>>>` split. It has to be written with the
      -- value in its *wrapped* form: an integer literal is not normalised to the
      -- dialect's width on the way in, so `0xF0000000` is the positive `4026531840` in
      -- Core, and on a non-negative value the two shifts agree by definition. `1 << 31`
      -- is `INT_MIN`, and there the two disagree, which is the point.
      --   `int x = 1 << 31; x >> 4`       cc: -134217728
      --   `unsigned u = 1u << 31; u >> 4` cc:  134217728
    , { name := "ns.sarMin", params := [],
        body := .ret (.binop ">>" (.binop "<<" (.lit (.int 1)) (.lit (.int 31)))
                                  (.lit (.int 4))) }
    , { name := "ns.shrMin", params := [],
        body := .ret (.binop ">>>" (.binop "<<" (.lit (.int 1)) (.lit (.int 31)))
                                   (.lit (.int 4))) }
      -- `int a[] = {7,8,9}; return a[1] ^ a[2];`
    , { name := "ns.tbl",   params := [],
        body := .ret (.binop "^" (.index (.listE [.lit (.int 7), .lit (.int 8),
                                                  .lit (.int 9)]) (.lit (.int 1)))
                                 (.index (.listE [.lit (.int 7), .lit (.int 8),
                                                  .lit (.int 9)]) (.lit (.int 2)))) }
      -- `struct crypto_alg alg = { .cra_priority = 100, .cra_name = "842" };
      --  return alg.cra_priority;`
    , { name := "ns.desig", params := [],
        body := .seq (.assign "alg" (.dictE [(.lit (.str "cra_priority"), .lit (.int 100)),
                                             (.lit (.str "cra_name"), .lit (.str "842"))]))
                     (.ret (.field (.name "alg") "cra_priority")) }
      -- A field the initializer does not mention is a hole, not `unit`.
    , { name := "ns.desigMissing", params := [],
        body := .seq (.assign "alg" (.dictE [(.lit (.str "cra_priority"),
                                              .lit (.int 100))]))
                     (.ret (.field (.name "alg") "cra_flags")) }
    , { name := "ns.forSum", params := []
      , body :=
          .seq (.assign "s" (.lit (.int 0)))
          (.seq (.assign "i" (.lit (.int 0)))
          (.seq (.loop (.binop "<" (.name "i") (.lit (.int 10)))
                  (.seq
                    -- the body, with `step; continue` in place of each `continue`
                    (.seq (.ifte (.binop "=="
                                    (.binop "%" (.name "i") (.lit (.int 3)))
                                    (.lit (.int 0)))
                            (.seq (.assign "i" (.binop "+" (.name "i") (.lit (.int 1))))
                                  .cont)
                            .skip)
                          (.assign "s" (.binop "+" (.name "s") (.name "i"))))
                    -- the step
                    (.assign "i" (.binop "+" (.name "i") (.lit (.int 1))))))
                (.ret (.binop "+" (.binop "*" (.name "s") (.lit (.int 100)))
                                  (.name "i"))))) }
    , { name := "ns.forNaive", params := []
      , body :=
          .seq (.assign "s" (.lit (.int 0)))
          (.seq (.assign "i" (.lit (.int 0)))
          (.seq (.loop (.binop "<" (.name "i") (.lit (.int 10)))
                  (.seq
                    (.seq (.ifte (.binop "=="
                                    (.binop "%" (.name "i") (.lit (.int 3)))
                                    (.lit (.int 0)))
                            .cont
                            .skip)
                          (.assign "s" (.binop "+" (.name "s") (.name "i"))))
                    (.assign "i" (.binop "+" (.name "i") (.lit (.int 1))))))
                (.ret (.binop "+" (.binop "*" (.name "s") (.lit (.int 100)))
                                  (.name "i"))))) }
      -- `for (j = 0; j < 10; j++) { if (j == 4) break; t += j; }` — `break` must *not*
      -- run the step, so `j` is left at 4. `cc` prints `t=6 j=4`.
    , { name := "ns.forBrk", params := []
      , body :=
          .seq (.assign "t" (.lit (.int 0)))
          (.seq (.assign "j" (.lit (.int 0)))
          (.seq (.loop (.binop "<" (.name "j") (.lit (.int 10)))
                  (.seq
                    (.seq (.ifte (.binop "==" (.name "j") (.lit (.int 4))) .brk .skip)
                          (.assign "t" (.binop "+" (.name "t") (.name "j"))))
                    (.assign "j" (.binop "+" (.name "j") (.lit (.int 1))))))
                (.ret (.binop "+" (.binop "*" (.name "t") (.lit (.int 100)))
                                  (.name "j"))))) }
      -- The kernel error-handling shape:
      --
      --     err = 0; err = 7; if (err) goto out; err = 100; out: err = err + 1;
      --     return err;
      --
      -- as `methodBody` encodes it: `while (true) { prefix; break } suffix`. The jump
      -- must skip `err = 100` and still run `err = err + 1`, so the answer is 8. `100`
      -- would mean the jump did not happen and `7` that the tail did not run.
    , { name := "ns.gotoOut", params := []
      , body :=
          .seq (.loop (.lit (.bool true))
                 (.seq (.seq (.assign "err" (.lit (.int 7)))
                        (.seq (.ifte (.name "err") .brk .skip)
                              (.assign "err" (.lit (.int 100)))))
                       .brk))
               (.seq (.assign "err" (.binop "+" (.name "err") (.lit (.int 1))))
                     (.ret (.name "err"))) }
      -- The same shape with the jump not taken: the wrapper must be transparent.
    , { name := "ns.gotoFall", params := []
      , body :=
          .seq (.loop (.lit (.bool true))
                 (.seq (.seq (.assign "err" (.lit (.int 0)))
                        (.seq (.ifte (.name "err") .brk .skip)
                              (.assign "err" (.lit (.int 100)))))
                       .brk))
               (.seq (.assign "err" (.binop "+" (.name "err") (.lit (.int 1))))
                     (.ret (.name "err"))) }
      -- And a `return` from inside the wrapper, which must leave the *function*, not the
      -- synthetic loop: `cc` returns 5, never reaching the tail.
    , { name := "ns.gotoRet", params := []
      , body :=
          .seq (.loop (.lit (.bool true))
                 (.seq (.seq (.assign "err" (.lit (.int 5)))
                             (.ret (.name "err")))
                       .brk))
               (.seq (.assign "err" (.lit (.int 99))) (.ret (.name "err"))) } ] }

/-- The same designated-initializer program under `.python`, where `d.f` on a dict is an
`AttributeError` and must stay a hole. `Dialect.fieldsOnDicts` is the switch. -/
private def pyDesig : Program := { cBits with dialect := .python }

-- `0x5A ^ 0x3C` — cc: 102
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 102) -/
#guard_msgs in #eval runFunc cBits 200 "ns.xor" []
-- `-1 & 255` — cc: 255.  Not `-1`, and not a boolean.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 255) -/
#guard_msgs in #eval runFunc cBits 200 "ns.and" []
-- `0xF0 | 0x0F` — cc: 255
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 255) -/
#guard_msgs in #eval runFunc cBits 200 "ns.or" []
-- `~0x5A` — cc: -91.  Under the old `<operator>.not -> "!"` mapping this was `false`.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-91)) -/
#guard_msgs in #eval runFunc cBits 200 "ns.bnot" []
-- `1 << 31` — cc -fwrapv: -2147483648
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-2147483648)) -/
#guard_msgs in #eval runFunc cBits 200 "ns.shl" []
-- `-8 >> 1` — cc: -4 (arithmetic, sign-extending)
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-4)) -/
#guard_msgs in #eval runFunc cBits 200 "ns.sar" []
-- `-1 >> 4` — cc: -1
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-1)) -/
#guard_msgs in #eval runFunc cBits 200 "ns.sarNeg" []
-- `0x80000000u >> 31` — cc: 1 (logical, zero-filling)
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 1) -/
#guard_msgs in #eval runFunc cBits 200 "ns.shrU" []
-- ... and the same bits reached by `1 << 31`, which Core stores as a negative number.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 1) -/
#guard_msgs in #eval runFunc cBits 200 "ns.shrUw" []
-- `0xF0000000u >> 4` — cc: 251658240
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 251658240) -/
#guard_msgs in #eval runFunc cBits 200 "ns.shrU4" []
-- The negative control: on `INT_MIN` the arithmetic shift keeps the sign bits and the
-- logical one does not. `>>` and `>>>` are two operators, and this is the difference.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-134217728)) -/
#guard_msgs in #eval runFunc cBits 200 "ns.sarMin" []
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 134217728) -/
#guard_msgs in #eval runFunc cBits 200 "ns.shrMin" []
-- `int a[] = {7,8,9}; a[1] ^ a[2]` — cc: 1
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 1) -/
#guard_msgs in #eval runFunc cBits 200 "ns.tbl" []
-- A designated initializer read back by field name: 100, not `unit` and not a hole.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 100) -/
#guard_msgs in #eval runFunc cBits 200 "ns.desig" []
-- A field the aggregate does not carry: a hole naming it, never an invented `unit`.
/-- info: Autoform.Core.EResult.hole "field:cra_flags:absent-from-aggregate" -/
#guard_msgs in #eval runFunc cBits 200 "ns.desigMissing" []
-- The dialect split. `{'cra_priority': 100}.cra_priority` is an `AttributeError` in
-- Python, so under `.python` the same term is the hole it has always been.
/-- info: Autoform.Core.EResult.hole "field:cra_priority:non-object" -/
#guard_msgs in #eval runFunc pyDesig 200 "ns.desig" []
-- The `for` with `continue`: `s = 27`, `i = 10` — cc: `forcont s=27 i=10`.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 2710) -/
#guard_msgs in #eval runFunc cBits 4000 "ns.forSum" []
-- The negative control. The textbook desugaring skips the step on `continue` and spins
-- forever; four thousand steps of fuel are not enough because no number of them is.
/-- info: Autoform.Core.EResult.outOfFuel -/
#guard_msgs in #eval runFunc cBits 4000 "ns.forNaive" []
-- The `for` with `break`: `t = 6`, `j = 4` — cc: `forbrk t=6 j=4`. `break` leaves
-- without running the step, which is why `j` is 4 and not 5.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 604) -/
#guard_msgs in #eval runFunc cBits 4000 "ns.forBrk" []
-- `goto out` taken: skips the middle, runs the tail. cc: 8.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 8) -/
#guard_msgs in #eval runFunc cBits 400 "ns.gotoOut" []
-- ... not taken: falls through the whole prefix, then the tail. cc: 101.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 101) -/
#guard_msgs in #eval runFunc cBits 400 "ns.gotoFall" []
-- ... and a `return` inside the wrapper leaves the function, not the synthetic loop.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 5) -/
#guard_msgs in #eval runFunc cBits 400 "ns.gotoRet" []

end CEvidence

/-! ## Modules as objects, end to end

The exporter represents an imported module as a **heap object** whose class name begins
`<module>` and whose fields are the module's top-level functions, classes and submodules,
allocated once by a synthetic initializer that `render_lean.py` places first in
`moduleInits`. Nothing was added to `Core` for it: `Expr.alloc`, `Stmt.setField` and
`Expr.field` already do the work.

The program below is the translation of a two-file package, in the exact shape
`cartographer/export_ast.sc` emits:

```python
# pkg/util.py
def double(n):
    return n * 2

# main
import pkg.util
pkg.util.double(21)      # 42
pkg.util.double          # <function double at ...>
pkg.util.VERSION         # AttributeError
```

Measured with CPython 3.9.6:

```
42
<function double at 0x109796af0>
AttributeError: module 'pkg.util' has no attribute 'VERSION'
```

The three checks below are the non-vacuity evidence. A module object with no fields, or
one whose fields never resolved, would answer `unit` to all three while every downstream
theorem still passed. -/
def modProg : Program :=
  { dialect := .python
  , funcs :=
    [ { name := "pkg/util.py:<module>.double", params := ["n"]
      , body := .ret (.binop "*" (.name "n") (.lit (.int 2))) }
      -- `pkg.util.double(21)`: a field read through the package object into the submodule
      -- object, then a call of the function that submodule's field holds.
    , { name := "main.run", params := []
      , body := .ret (.mcall (.field (.name "<module>pkg/__init__.py") "util")
                             "double" [.lit (.int 21)]) }
      -- `pkg.util.double` as a *value*: nesting resolves without calling anything.
    , { name := "main.ref", params := []
      , body := .ret (.field (.field (.name "<module>pkg/__init__.py") "util") "double") }
      -- `pkg.util.VERSION`: a module-level name the module object deliberately does not
      -- carry. CPython raises `AttributeError`; Core refuses. Refusing is not the same
      -- claim as raising, so it is a hole and not an `exn`.
    , { name := "main.attr", params := []
      , body := .ret (.field (.field (.name "<module>pkg/__init__.py") "util") "VERSION") } ] }

/-- The synthetic `<module-objects>` initializer: **all** allocations first, then the
field writes, so a package and a module that import each other both exist before either
is populated. -/
def modInit : Func :=
  { name := "<module-objects>:<module>", params := []
  , body :=
      .seq (.setGlobal "<module>pkg/__init__.py" (.alloc "<module>pkg/__init__.py" []))
      (.seq (.setGlobal "<module>pkg/util.py" (.alloc "<module>pkg/util.py" []))
      (.seq (.setField (.name "<module>pkg/__init__.py") "util"
                       (.name "<module>pkg/util.py"))
            (.setField (.name "<module>pkg/util.py") "double"
                       (.fnref "pkg/util.py:<module>.double")))) }

/-! `pkg.util.double(21)` is `42`, as CPython prints. `unit` would mean a field read
missed; a hole would mean the module object never reached the call. -/
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 42) -/
#guard_msgs in #eval runMain modProg 200 [modInit] "main.run" []

/-! Nesting: the package's `util` field holds the submodule object, whose `double` field
holds the function value. -/
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.fn "pkg/util.py:<module>.double") -/
#guard_msgs in #eval runMain modProg 200 [modInit] "main.ref" []

/-! The honesty check, and the reason a module object carries a marker class at all. An
ordinary object answers `unit` for a field it does not have (`ns.unset`, above); a module
object names the miss. Module-level *data* is absent from a module object on purpose —
Core has one globals frame for the whole program, so a module-level constant is not
module-scoped and its value would have to be captured before the module body computed it
— and this is what stops that decision from becoming a silent `unit`. -/
/-- info: Autoform.Core.EResult.hole "module-attr:VERSION" -/
#guard_msgs in #eval runMain modProg 200 [modInit] "main.attr" []

/-! ## f-strings

`f'v{n}!'` is `"v" + str(n) + "!"` — that is the language definition for a field with no
conversion and no format spec, so the exporter emits exactly that. What it meets is a
Core limitation that predates it: `Stdlib.builtin`'s `str` answers on `.int` and `.bool`
and **declines on `.str`**, because Core represents an exception as a bare `Val.str` and
cannot tell one from an ordinary string.

So the f-string hole *moves* rather than vanishing, and both halves are pinned here.
Measured with CPython 3.9.6: `greet(3)` is `'v3!'` and `greet('x')` is `'vx!'`. -/
def fstrProg : Program :=
  { dialect := .python
  , funcs :=
    [ { name := "greet", params := ["n"]
      , body := .ret (.binop "+" (.binop "+" (.lit (.str "v")) (.call "str" [.name "n"]))
                                 (.lit (.str "!"))) } ] }

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.str "v3!") -/
#guard_msgs in #eval runFunc fstrProg 200 "greet" [.int 3]

/-! The residue, named for what actually blocks it. CPython answers `'vx!'`; Core answers
a hole at `str` rather than a wrong string, and the label points at `Stdlib`'s `str`, not
at the f-string. -/
/-- info: Autoform.Core.EResult.hole "call:str" -/
#guard_msgs in #eval runFunc fstrProg 200 "greet" [.str "x"]

end Autoform.Core
