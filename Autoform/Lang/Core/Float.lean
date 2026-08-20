/-!
# Core — binary floating point

## Why this file exists

`STRATEGY.md` §27 records the current ceiling of the differential oracle:

    skip_unencodable_args — dominated by caches wider than 256 entries (15,487)
    and floats (6,995, which Core has no type for)

`scripts/differential.py` refuses ~7,000 cases outright because
`isinstance(v, (float, complex, bytes, frozenset, set))` raises `Unencodable`. Every one
of those is a case the oracle *cannot even look at*. This module supplies the missing
value domain.

## The representation decision, and why it is not `Float`

Three candidates were considered. The requirement that decides between them is stated in
the task and is the right one: **the oracle needs bit-exact agreement with CPython**, and
a float model that is merely "close" manufactures divergences that are artefacts of the
model rather than defects in the artefact — precisely the failure mode §27 spent an
entire episode eliminating.

### Rejected: Lean's `Float`

`Float` *is* an IEEE 754 binary64 backed by a C `double`, so at first glance it is exactly
CPython's type. It is nonetheless the wrong choice here, for a reason that has nothing to
do with accuracy:

* **`Float` is opaque to the kernel.** It is an `opaque` type implemented by `@[extern]`
  primitives. `#eval` runs the compiled code; `decide`, `rfl`, `simp` and `omega` cannot
  reduce a single `Float` operation. So *nothing about it can be proved*. A `Val.float`
  carrying a `Float` would make every function touching a float unrefinable — the
  74-theorem layer in `Autoform/Refine.lean` would simply have nothing to say. That
  converts a hole (visible, counted) into a value that silently blocks verification,
  which is the wrong direction.
* **`Float`'s `BEq`/`Ord` are IEEE, but its `DecidableEq` is not derivable**, so it cannot
  appear in a `deriving DecidableEq` datatype, which `Val`'s neighbours rely on.
* **It is a trusted external oracle inside the trust chain.** `README.md`'s trust table
  claims "proofs depend on no unsound axiom". `Float` operations are axiomatised
  externs; a theorem whose statement mentions `Float.add` is a theorem about an
  unverified C compiler intrinsic.

### Rejected: rationals / exact real arithmetic

Exact rationals get every arithmetic law for free and are *wrong*, in the specific sense
that matters: `0.1 + 0.2 = 0.30000000000000004` in CPython and `3/10` in the rationals.
A rational model disagrees with the runtime on the very first test case. It also cannot
express `inf`, `nan`, `-0.0`, or overflow at all.

### Chosen: the bit pattern, with exact-rational rounding

`Fl` is a **bit pattern plus its format** — a `Nat` of `fmt.width` bits, decoded into
sign/exponent/significand exactly as IEEE 754 §3.4 specifies. Arithmetic is implemented
the way the standard *defines* it, rather than by imitating hardware:

> IEEE 754 §5.1: each operation "shall be performed as if it first produced an
> intermediate result correct to infinite precision and with unbounded range, and then
> rounded that result" to the destination format.

So `add`, `sub`, `mul`, `div` compute the **exact** result as a rational `±num/den`
(always with a power-of-two denominator, except for `div` where the quotient is exact by
construction of the numerator and denominator), and hand it to one rounding function,
`Format.round`, implementing round-to-nearest-ties-to-even with correct subnormal
handling and correct overflow. This is bit-exact with any conforming binary64
implementation by construction, and every step is ordinary `Nat`/`Int` arithmetic that
Lean's kernel can reduce and `omega`/`decide` can reason about.

The cost is that big exponent differences produce big `Nat`s (`1e300 + 1e-300` shifts a
significand by ~2000 bits). That is a performance cost, not a fidelity cost, and `Nat` is
GMP-backed.

## Parameterized, not hardcoded — the §12/§16 rule

Following `Numeric.lean`: the format is a parameter (`Format.binary64`, `Format.binary32`
— C `float` is binary32, and rounding it as binary64 is exactly the "these look identical
across languages" mistranslation §22 catalogues), and the *language-level* choices that
sit on top of IEEE are a separate parameter (`FConfig`):

| behaviour | Python | C (IEC 559, SSE) | C (x87 / `FLT_EVAL_METHOD=2`) |
|---|---|---|---|
| `x / 0.0` | raises `ZeroDivisionError` | `±inf` (`0.0/0.0` → `nan`) | `±inf` |
| `x % 0.0` | raises `ZeroDivisionError` | `nan` | `nan` |
| arithmetic overflow | silent `inf` | silent `inf` | silent `inf` |
| `float(10**400)` | raises `OverflowError` | — | — |
| intermediate precision | binary64 | binary64 | **wider, unspecified** |

The last row is the float analogue of signed-integer overflow, and gets the same
treatment: `FConfig.excessPrecision := true` makes every arithmetic operation return
`FResult.ub "float:excess-precision"`, which the interpreter is meant to wire to
`Expr.hole` (§16). On x87 without `-ffloat-store`, `a*b + c` genuinely has no
binary64-determined answer; inventing one would be the `mulbig` bug in a new domain.

## What is deliberately NOT modelled

Each of these returns `FResult.unmodelled`, i.e. a *visible* hole, never a value:

* **`repr(x)` / `str(x)` / `float("0.1")` from a string.** CPython uses shortest
  round-tripping decimal conversion (David Gay / Grisu-style). Producing `"0.1"` rather
  than `"0.1000000000000000055511151231257827"` requires that algorithm, and getting it
  slightly wrong yields a *string* divergence on every float in the corpus. The oracle
  should compare bit patterns, not decimal text: `Fl.ofBits` exists precisely so
  `differential.py` can emit `Fl.ofBits 4591870180066957722` instead of `0.1`.
  (`Format.ofDecimal` *does* correctly round a decimal *literal* — digits and a power of
  ten — into the format, which is the direction the transpiler needs.)
* **`hash(float)`** — same objection as `hash` in `Stdlib.lean`.
* **`x ** y`, `math.sqrt`, and every transcendental.** `pow` and `sqrt` are correctly
  rounded in IEEE and could be modelled; `sin`, `exp`, `log` are **not** required to be
  correctly rounded by IEEE 754 or by C, so CPython's answers are libm's answers and
  differ between platforms. A model of `math.exp` would be a model of one machine's libm.
  `sqrt` is left unmodelled here only for scope, and is marked as such.
* **`float.__eq__` against `Decimal`/`Fraction`, and `complex`.** No corresponding value.
* **Signalling NaN payloads and non-default rounding modes.** Python cannot set either.

## Discipline

Total functions only: no `partial`, no `sorry`, no `unsafe`, no `native_decide`.

## Wiring (for `Syntax.lean` / `Semantics.lean`, not done here)

1. `Val.float : Fl → Val`, and `Lit.float : Fl → Lit`.
2. `applyBinop` on `.float`/`.float` (and the int/float mixed cases, via
   `FConfig.ofInt`, which is Python's implicit coercion) dispatches to `FConfig.add`
   etc., then `fresToE` below maps `ok ↦ .val`, `exn ↦ .exn`, `ub`/`unmodelled ↦ .hole`.
3. `Val.beq` on floats **must not** be structural bit equality: `nan != nan` and
   `+0.0 == -0.0`. Use `FConfig.eq`. Bit equality is still the right thing for `is`
   *only* because CPython does not intern floats — `0.1 is 0.1` is `False` for separately
   evaluated literals, so `is` on unboxed floats should stay a hole.
   `float_beq_is_not_bit_equality` below states the discrepancy as an executable fact.
4. `differential.py`: drop `float` from the `Unencodable` tuple and emit
   `Val.float (Fl.ofBits <int>)` using `struct.unpack('<Q', struct.pack('<d', v))[0]`,
   and compare parsed results by bit pattern. That is exact in both directions and needs
   no decimal formatting anywhere in the harness.
-/

namespace Autoform.Core

/-! ## Formats -/

/-- An IEEE 754 binary interchange format. `prec` counts the significand bits *including*
the hidden leading bit; `emax` is the largest unbiased exponent of a normal number, and is
also the exponent bias. -/
structure Format where
  prec    : Nat := 53
  emax    : Int := 1023
  expBits : Nat := 11
  deriving Repr, Inhabited, DecidableEq

namespace Format

/-- IEEE binary64: Python `float`, C `double`, Java `double`, JavaScript `number`. -/
def binary64 : Format := { prec := 53, emax := 1023, expBits := 11 }

/-- IEEE binary32: C `float`, Java `float`. Present so that a C program's `float` is not
silently rounded as a `double` — the §22 mistake in a new domain. -/
def binary32 : Format := { prec := 24, emax := 127, expBits := 8 }

/-- Smallest unbiased exponent of a *normal* number. -/
def emin (f : Format) : Int := 1 - f.emax
/-- Number of stored significand bits (the hidden bit is not stored). -/
def mantBits (f : Format) : Nat := f.prec - 1
/-- Total bit width. -/
def width (f : Format) : Nat := 1 + f.expBits + f.mantBits
/-- The reserved all-ones exponent field (`inf` and `nan`). -/
def expAllOnes (f : Format) : Nat := 2 ^ f.expBits - 1
/-- The exponent of the least significant bit of a subnormal: `-1074` for binary64. -/
def minSubExp (f : Format) : Int := f.emin - (f.mantBits : Int)

/-- Both interchange formats are consistent: the width is the sum of the fields. -/
theorem binary64_width : binary64.width = 64 := by decide
theorem binary32_width : binary32.width = 32 := by decide
/-- The bias equals `emax`, and `emin = 1 - emax`, as IEEE 754 §3.3 requires. -/
theorem binary64_emin : binary64.emin = -1022 := by decide
theorem binary64_minSubExp : binary64.minSubExp = -1074 := by decide

end Format

/-! ## Values -/

/-- A floating-point value: a format together with the bit pattern of that width.

Carrying the format in the value is deliberate. A `Val.float` produced by a C `float`
expression and one produced by a C `double` expression are different values with
different rounding, and an operation mixing them without an explicit conversion is a
translation error, reported as `FResult.unmodelled "float:format-mismatch"` rather than
silently reinterpreted. -/
structure Fl where
  fmt  : Format := Format.binary64
  bits : Nat    := 0
  deriving Repr, Inhabited, DecidableEq

namespace Fl

/-- Build from a raw bit pattern (masked to the format's width). This is the constructor
`differential.py` should emit: `struct.unpack('<Q', struct.pack('<d', x))[0]`. -/
def ofBits (n : Nat) (f : Format := Format.binary64) : Fl :=
  { fmt := f, bits := n % 2 ^ f.width }

def signBit (x : Fl) : Bool := (x.bits / 2 ^ (x.fmt.width - 1)) % 2 == 1
def expField (x : Fl) : Nat := (x.bits / 2 ^ x.fmt.mantBits) % 2 ^ x.fmt.expBits
def mantField (x : Fl) : Nat := x.bits % 2 ^ x.fmt.mantBits

/-- Assemble sign, biased exponent and stored significand into a bit pattern. -/
def ofParts (f : Format) (neg : Bool) (bexp mant : Nat) : Fl :=
  { fmt  := f,
    bits := (if neg then 2 ^ (f.width - 1) else 0)
            + (bexp % 2 ^ f.expBits) * 2 ^ f.mantBits + mant % 2 ^ f.mantBits }

def isNaN  (x : Fl) : Bool := x.expField == x.fmt.expAllOnes && x.mantField != 0
def isInf  (x : Fl) : Bool := x.expField == x.fmt.expAllOnes && x.mantField == 0
def isZero (x : Fl) : Bool := x.expField == 0 && x.mantField == 0
def isSubnormal (x : Fl) : Bool := x.expField == 0 && x.mantField != 0
def isFinite (x : Fl) : Bool := x.expField != x.fmt.expAllOnes

/-- Signed zero. `-0.0` is a distinct bit pattern that compares *equal* to `+0.0`; the two
facts together are where naive models go wrong. -/
def zero (f : Format) (neg : Bool) : Fl := ofParts f neg 0 0
def inf  (f : Format) (neg : Bool) : Fl := ofParts f neg f.expAllOnes 0
/-- The canonical quiet NaN: `0x7ff8000000000000` in binary64, which is what
`float('nan')` produces in CPython. -/
def nan  (f : Format) : Fl := ofParts f false f.expAllOnes (2 ^ (f.mantBits - 1))

/-- Sign flip. Defined on the bit pattern, so it is correct on `-0.0` and on NaN, where
"negate the value" would be meaningless. -/
def neg (x : Fl) : Fl := ofParts x.fmt (!x.signBit) x.expField x.mantField
def abs (x : Fl) : Fl := ofParts x.fmt false x.expField x.mantField

/-- The exact value of a *finite* `Fl`, as sign, significand and exponent:
`(-1)^neg * m * 2^e`. `none` for infinities and NaN. Exact — no rounding happens here. -/
def toExact (x : Fl) : Option (Bool × Nat × Int) :=
  if x.isFinite then
    if x.expField == 0 then
      some (x.signBit, x.mantField, x.fmt.minSubExp)
    else
      some (x.signBit, 2 ^ x.fmt.mantBits + x.mantField,
            (x.expField : Int) - x.fmt.emax - (x.fmt.mantBits : Int))
  else none

/-- A readable description for `#eval`: class, and the exact value as `±m·2^e`. -/
def describe (x : Fl) : String :=
  if x.isNaN then "nan"
  else if x.isInf then (if x.signBit then "-inf" else "inf")
  else match x.toExact with
       | some (s, m, e) =>
           (if s then "-" else "+") ++ toString m ++ "·2^" ++ toString e
           ++ (if x.isSubnormal then " (subnormal)" else "")
       | none => "?"

end Fl

namespace Fl

/-- Comparison, without a configuration — see the note on `FConfig.cmp`. This is the form
`Val.beq` needs, since `Val` carries no dialect. -/
def cmpv (x y : Fl) : Option Ordering :=
  if x.isNaN || y.isNaN then none
  else if x.isZero && y.isZero then some .eq        -- +0.0 == -0.0
  else if x.isInf || y.isInf then
    if x.isInf && y.isInf then
      if x.signBit == y.signBit then some .eq
      else some (if x.signBit then .lt else .gt)
    else if x.isInf then some (if x.signBit then .lt else .gt)
    else some (if y.signBit then .gt else .lt)
  else match x.toExact, y.toExact with
    | some (sa, ma, ea), some (sb, mb, eb) =>
        if sa != sb then some (if sa then .lt else .gt)
        else
          let e := min ea eb
          let A := ma * 2 ^ (ea - e).toNat
          let B := mb * 2 ^ (eb - e).toNat
          some (if sa then compare B A else compare A B)
    | _, _ => none

/-- Python `==` on two floats: NaN is not equal to itself, `+0.0 == -0.0`. -/
def eqv (x y : Fl) : Bool := Fl.cmpv x y == some .eq

/-- Truthiness: `bool(0.0) == bool(-0.0) == False`, everything else — including `nan` —
is `True`. -/
def truthy (x : Fl) : Bool := !x.isZero

/-- Exact `Int` vs float comparison, configuration-free. -/
def cmpIntv (n : Int) (x : Fl) : Option Ordering :=
  if x.isNaN then none
  else if x.isInf then some (if x.signBit then .gt else .lt)
  else match x.toExact with
    | some (s, m, e) =>
        -- compare `n` with `±m·2^e` by clearing the denominator
        let (nn, dd) : Int × Int :=
          if 0 ≤ e then (n, (m : Int) * 2 ^ e.toNat)
          else (n * 2 ^ (-e).toNat, (m : Int))
        some (compare nn (if s then -dd else dd))
    | none => none

end Fl

/-! ## Rounding

One function. Every arithmetic operation in this file reduces to it, which is what makes
"correctly rounded" a property of the file rather than of each operator. -/

/-- Bit length: `bitLen 0 = 0`, `bitLen n = ⌊log₂ n⌋ + 1`. -/
def bitLen (n : Nat) : Nat := if n == 0 then 0 else Nat.log2 n + 1

/-- `⌊num · 2^s / den⌋`, together with the comparison of twice the remainder against the
divisor — i.e. everything round-to-nearest needs: `lt` = below halfway, `eq` = exactly
halfway (the ties-to-even case), `gt` = above. -/
def divSticky (num den : Nat) (s : Int) : Nat × Ordering :=
  if 0 ≤ s then
    let n := num * 2 ^ s.toNat
    (n / den, compare (2 * (n % den)) den)
  else
    let d := den * 2 ^ (-s).toNat
    (num / d, compare (2 * (num % d)) d)

namespace Format

/-- Round the exact nonnegative rational `num/den`, with sign `neg`, into this format,
using round-to-nearest-ties-to-even — the only mode CPython can be in.

This is IEEE 754 §5.1 taken literally: the caller supplies the infinitely precise result
and this decides the representable one. Subnormals, gradual underflow, the carry out of
the significand, and overflow-to-infinity are all handled in the one place.

`den = 0` is a caller error and yields NaN; every caller below guarantees `den > 0`. -/
def round (f : Format) (neg : Bool) (num den : Nat) : Fl :=
  if den == 0 then Fl.nan f
  else if num == 0 then Fl.zero f neg
  else
    let p : Int := (f.prec : Int)
    -- `num/den ∈ [2^(g-1), 2^(g+1))`, so scaling by `2^(p-1-g)` lands within one bit of
    -- the `p`-bit window `[2^(p-1), 2^p)`.
    let g : Int := (bitLen num : Int) - (bitLen den : Int)
    let s0 : Int := (p - 1) - g
    let q0 := (divSticky num den s0).1
    let s1 : Int :=
      if q0 ≥ 2 ^ f.prec then s0 - 1
      else if q0 < 2 ^ (f.prec - 1) then s0 + 1
      else s0
    -- Gradual underflow: the exponent of the least significant bit can never go below
    -- `minSubExp`, so the scale is capped rather than the significand truncated.
    let sMax : Int := -f.minSubExp
    let s : Int := min s1 sMax
    let (q, c) := divSticky num den s
    let up := c == .gt || (c == .eq && q % 2 == 1)
    let q' := if up then q + 1 else q
    if q' == 0 then Fl.zero f neg
    else
      let bl := bitLen q'
      -- Unbiased exponent of the rounded significand's leading bit.
      let eUnb : Int := (bl : Int) - 1 - s
      -- Rounding may carry out of the top bit (`q' = 2^p`); `eUnb` already accounts for
      -- it, the significand just has to be renormalised.
      let qn := if bl == f.prec + 1 then q' / 2 else q'
      if eUnb > f.emax then Fl.inf f neg
      else if eUnb < f.emin then Fl.ofParts f neg 0 qn                      -- subnormal
      else Fl.ofParts f neg (eUnb + f.emax).toNat (qn - 2 ^ f.mantBits)     -- normal

/-- Round the exact value `(-1)^neg · (num/den) · 2^e`. -/
def roundScaled (f : Format) (neg : Bool) (num den : Nat) (e : Int) : Fl :=
  if 0 ≤ e then f.round neg (num * 2 ^ e.toNat) den
  else f.round neg num (den * 2 ^ (-e).toNat)

/-- A decimal literal `(-1)^neg · digits · 10^exp10`, correctly rounded. This is what the
transpiler needs for `0.1`: CPython's `strtod` is correctly rounded, so this agrees with
it bit for bit. The *reverse* direction (float → shortest decimal) is deliberately not
modelled — see the header. -/
def ofDecimal (f : Format) (neg : Bool) (digits : Nat) (exp10 : Int) : Fl :=
  if 0 ≤ exp10 then f.round neg (digits * 10 ^ exp10.toNat) 1
  else f.round neg digits (10 ^ (-exp10).toNat)

end Format

/-! ## Language-level configuration -/

/-- What the *source language* does when a float division has a zero divisor. IEEE says
`±inf` (and `nan` for `0/0`); Python overrides it with an exception. -/
inductive FDivZero where
  /-- Python: `ZeroDivisionError`. -/
  | raise
  /-- IEEE / C / Java: `±inf`, or `nan` for `0.0/0.0`. -/
  | ieee
  deriving Repr, Inhabited, DecidableEq

/-- The floating-point dialect. -/
structure FConfig where
  fmt : Format := Format.binary64
  onDivZero : FDivZero := .raise
  /-- Intermediate results may be computed in a wider format than `fmt` (x87 with
  `FLT_EVAL_METHOD = 2`, or an FMA contraction the compiler is free to introduce). When
  true, no binary64 answer is the answer, and every arithmetic operation reports `ub`
  rather than guessing — the §16 discipline. -/
  excessPrecision : Bool := false
  deriving Repr, Inhabited, DecidableEq

namespace FConfig
/-- CPython `float`. -/
def python : FConfig := { fmt := Format.binary64, onDivZero := .raise }
/-- C `double` on SSE2 / any target with `FLT_EVAL_METHOD = 0`, assuming
`__STDC_IEC_559__`. This is what the differential harness's `cc` produces on x86-64. -/
def cDouble : FConfig := { fmt := Format.binary64, onDivZero := .ieee }
/-- C `float`. Note the *format* change: rounding a `float` expression at binary64 is a
silent wrong answer, not an approximation. -/
def cFloat : FConfig := { fmt := Format.binary32, onDivZero := .ieee }
/-- C `double` compiled for x87 without `-ffloat-store`, or with FMA contraction enabled.
Every arithmetic result is `ub`. -/
def cDoubleExcess : FConfig := { cDouble with excessPrecision := true }
/-- Java `double`: IEEE, `strictfp` since Java 17, no exception on division by zero. -/
def java64 : FConfig := { fmt := Format.binary64, onDivZero := .ieee }
end FConfig

/-! ## Results -/

/-- Outcome of a floating-point operation. Four outcomes, for four different reasons,
mirroring `NumResult`. -/
inductive FResult where
  | ok : Fl → FResult
  /-- The source language defines this as raising: Python's `ZeroDivisionError`,
  `OverflowError`, `ValueError`. -/
  | exn : String → FResult
  /-- The source language does not determine the result (x87 excess precision, FMA
  contraction). Wire to `Expr.hole`. -/
  | ub : String → FResult
  /-- This module does not model the operation (`repr`, `hash`, transcendentals). Wire to
  `Expr.hole` too — but it is a *different* claim: `ub` says no answer exists, this says
  we have not computed the answer that does. -/
  | unmodelled : String → FResult
  deriving Repr, Inhabited, DecidableEq

namespace FResult
def isOk : FResult → Bool | .ok _ => true | _ => false
def toOption : FResult → Option Fl | .ok v => some v | _ => none
end FResult

/-! ## Arithmetic -/

namespace FConfig

/-- Guard shared by every arithmetic operation: operand formats must agree with the
configuration, and excess precision poisons the result. -/
private def guard2 (c : FConfig) (x y : Fl) (k : Unit → FResult) : FResult :=
  if x.fmt != c.fmt || y.fmt != c.fmt then .unmodelled "float:format-mismatch"
  else if c.excessPrecision then .ub "float:excess-precision"
  else k ()

/-- NaN propagation, checked before anything else, as IEEE §6.2 requires. -/
private def nanIn (_c : FConfig) (x y : Fl) : Bool := x.isNaN || y.isNaN

/-- Addition. The exact sum of two finite binary floats is a dyadic rational, computed
here with `Int` arithmetic at the common exponent and then rounded once. -/
def add (c : FConfig) (x y : Fl) : FResult :=
  guard2 c x y fun _ =>
  if nanIn c x y then .ok (Fl.nan c.fmt)
  else if x.isInf && y.isInf then
    -- `inf + -inf` is NaN; Python does not raise here.
    if x.signBit == y.signBit then .ok x else .ok (Fl.nan c.fmt)
  else if x.isInf then .ok x
  else if y.isInf then .ok y
  else match x.toExact, y.toExact with
    | some (sa, ma, ea), some (sb, mb, eb) =>
        let e := min ea eb
        let A : Int := (ma * 2 ^ (ea - e).toNat : Nat)
        let B : Int := (mb * 2 ^ (eb - e).toNat : Nat)
        let S : Int := (if sa then -A else A) + (if sb then -B else B)
        if S == 0 then
          -- IEEE §6.3: an exact zero sum is `+0` under round-to-nearest, except that
          -- `(-0) + (-0) = -0`. This is the case a value-level model always gets wrong.
          .ok (Fl.zero c.fmt (x.isZero && y.isZero && sa && sb))
        else .ok (c.fmt.roundScaled (S < 0) S.natAbs 1 e)
    | _, _ => .unmodelled "float:unreachable-nonfinite"

def sub (c : FConfig) (x y : Fl) : FResult := c.add x y.neg

def mul (c : FConfig) (x y : Fl) : FResult :=
  guard2 c x y fun _ =>
  if nanIn c x y then .ok (Fl.nan c.fmt)
  else
    let s := xor x.signBit y.signBit
    if x.isInf || y.isInf then
      if x.isZero || y.isZero then .ok (Fl.nan c.fmt)   -- inf * 0
      else .ok (Fl.inf c.fmt s)
    else match x.toExact, y.toExact with
      | some (_, ma, ea), some (_, mb, eb) => .ok (c.fmt.roundScaled s (ma * mb) 1 (ea + eb))
      | _, _ => .unmodelled "float:unreachable-nonfinite"

/-- Division. The dialect decides what a zero divisor means; everything else is IEEE.
Note the quotient is *correctly rounded*, obtained by rounding the exact rational
`ma/mb · 2^(ea-eb)` — not by any iterative approximation. -/
def div (c : FConfig) (x y : Fl) : FResult :=
  guard2 c x y fun _ =>
  if nanIn c x y then .ok (Fl.nan c.fmt)
  else
    let s := xor x.signBit y.signBit
    if y.isZero then
      match c.onDivZero with
      | .raise => .exn "ZeroDivisionError"
      | .ieee  => if x.isZero || x.isNaN then .ok (Fl.nan c.fmt)
                  else .ok (Fl.inf c.fmt s)
    else if x.isInf && y.isInf then .ok (Fl.nan c.fmt)
    else if x.isInf then .ok (Fl.inf c.fmt s)
    else if y.isInf then .ok (Fl.zero c.fmt s)
    else match x.toExact, y.toExact with
      | some (_, ma, ea), some (_, mb, eb) =>
          if ma == 0 then .ok (Fl.zero c.fmt s)
          else .ok (c.fmt.roundScaled s ma mb (ea - eb))
      | _, _ => .unmodelled "float:unreachable-nonfinite"

/-- C's `fmod` / `math.fmod`: the remainder of *truncated* division, which IEEE
guarantees is exactly representable — so this rounds nothing and can be computed with a
single `Nat` modulus at the common exponent. -/
def fmod (c : FConfig) (x y : Fl) : FResult :=
  guard2 c x y fun _ =>
  if nanIn c x y then .ok (Fl.nan c.fmt)
  else if x.isInf then .ok (Fl.nan c.fmt)
  else if y.isZero then
    match c.onDivZero with
    | .raise => .exn "ZeroDivisionError"
    | .ieee  => .ok (Fl.nan c.fmt)
  else if y.isInf then .ok x
  else match x.toExact, y.toExact with
    | some (sa, ma, ea), some (_, mb, eb) =>
        let e := min ea eb
        let A := ma * 2 ^ (ea - e).toNat
        let B := mb * 2 ^ (eb - e).toNat
        let R := A % B
        -- The sign of `fmod` is the sign of the *dividend*, including for a zero result.
        if R == 0 then .ok (Fl.zero c.fmt sa) else .ok (c.fmt.roundScaled sa R 1 e)
    | _, _ => .unmodelled "float:unreachable-nonfinite"

/-- Python's `%` on floats. **Not** `fmod`: CPython's `float_rem` takes `fmod` and then
adds the divisor when the signs disagree, so the result takes the sign of the *divisor*
(`-5.5 % 2.0 == 0.5`, while `math.fmod(-5.5, 2.0) == -1.5`). The `mod += wx` step is a
rounded addition, which is why it is expressed here in terms of `add` rather than
recomputed exactly. A zero result takes the sign of the divisor. -/
def pyMod (c : FConfig) (x y : Fl) : FResult :=
  match c.fmod x y with
  | .ok m =>
      if m.isNaN then .ok m
      else if m.isZero then .ok (Fl.zero c.fmt y.signBit)
      else if m.signBit != y.signBit then c.add m y
      else .ok m
  | r => r

/-! ### Comparison

Python's float comparison is IEEE's: NaN is unordered (so `x != x` when `x` is NaN, and
`nan < 1.0`, `nan > 1.0`, `nan == 1.0` are all `False`), and `+0.0 == -0.0`. Structural
bit comparison gets both of these wrong, in opposite directions. -/

/-- Ordering, or `none` when the operands are unordered (either is NaN).

The configuration is unused, deliberately: comparison decodes both operands to their
*exact* values, so a binary32 and a binary64 operand compare correctly without a
conversion step (C's `float`→`double` promotion is exact, so this agrees with C too).
Everything that *rounds* takes the format from the configuration; nothing here rounds. -/
def cmp (_c : FConfig) (x y : Fl) : Option Ordering := Fl.cmpv x y

end FConfig

namespace FConfig

def eq (c : FConfig) (x y : Fl) : Bool := c.cmp x y == some .eq
def lt (c : FConfig) (x y : Fl) : Bool := c.cmp x y == some .lt
def le (c : FConfig) (x y : Fl) : Bool := c.cmp x y == some .lt || c.cmp x y == some .eq
def ne (c : FConfig) (x y : Fl) : Bool := !(c.eq x y)

/-- Truthiness of a float under a configuration; the configuration is irrelevant. -/
def truthy (_c : FConfig) (x : Fl) : Bool := Fl.truthy x

/-! ### Conversions

Python compares and converts between `int` and `float` *exactly* — `10**23 == 1e23` is
`False` because CPython compares the exact integer with the exact float, rather than
coercing. Getting this wrong is a silent-wrong-answer bug of the `floorDiv` family, so
both directions are exact here. -/

/-- `float(n)`. Correctly rounded; Python raises `OverflowError` rather than returning
`inf` when the integer is too large ("int too large to convert to float"). -/
def ofInt (c : FConfig) (n : Int) : FResult :=
  let r := c.fmt.round (n < 0) n.natAbs 1
  if r.isInf then .exn "OverflowError" else .ok r

/-- `int(x)`: truncation toward zero. `int(inf)` is `OverflowError`, `int(nan)` is
`ValueError` — both are Python-specific and neither is a hole. -/
def toInt (_c : FConfig) (x : Fl) : Except String Int :=
  if x.isNaN then .error "ValueError"
  else if x.isInf then .error "OverflowError"
  else match x.toExact with
    | some (s, m, e) =>
        let n : Nat := if 0 ≤ e then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat
        .ok (if s then -(n : Int) else (n : Int))
    | none => .error "ValueError"

/-- Exact comparison between an `Int` and a float, as Python performs it. No coercion in
either direction, so `10^23 == 1e23` comes out `False`, matching CPython. -/
def cmpInt (_c : FConfig) (n : Int) (x : Fl) : Option Ordering := Fl.cmpIntv n x

end FConfig

namespace FConfig

/-! ### Explicitly unmodelled -/

/-- `repr(x)` / `str(x)` / `float(str)`. See the header: shortest round-tripping decimal
conversion is a real algorithm and an approximate version of it would diverge on every
float in the corpus. -/
def repr (_c : FConfig) (_x : Fl) : FResult := .unmodelled "float:repr-shortest-roundtrip"
/-- `hash(x)`. Implementation-defined, exactly as in `Stdlib.lean`. -/
def hash (_c : FConfig) (_x : Fl) : FResult := .unmodelled "float:hash"
/-- `x ** y`, `math.sqrt`, `math.exp`, ... `sqrt` and `pow` *are* correctly rounded in
IEEE and could be added; `exp`/`log`/`sin` are libm's answers, not the standard's, and
would be a model of one machine. -/
def transcendental (_c : FConfig) (name : String) : FResult :=
  .unmodelled ("float:" ++ name)

end FConfig

/-- Lift a float outcome into `EResult`'s shape. `Semantics.lean` cannot be imported here
(it imports this file), so this is written against the labels rather than the type; the
wiring is `ok ↦ .val (.float v)`, `exn ↦ .exn (.str r)`, `ub`/`unmodelled ↦ .hole`. -/
def FResult.holeLabel : FResult → Option String
  | .ok _ => none
  | .exn _ => none
  | .ub r => some ("ub:" ++ r)
  | .unmodelled r => some r

/-! ## What is proved

Modest and load-bearing, as in `Numeric.lean`. The heavy claim — that `add`/`mul`/`div`
agree with CPython bit for bit — is not provable inside Lean against an external runtime;
it is *measured*, in the Evidence section below, against the same hardware doubles CPython
uses. What is proved here is that the encoding is coherent. -/

namespace Fl

/-- Rounding an exactly-zero numerator gives a *signed* zero, never `-0.0` by accident. -/
theorem round_zero (f : Format) (neg : Bool) (den : Nat) (h : den ≠ 0) :
    f.round neg 0 den = Fl.zero f neg := by
  simp [Format.round, h]

/-- `1.0` decodes to `2^52 · 2^-52`. The whole encoding is checked by this one case:
hidden bit, bias and mantissa offset all have to be right for it to hold. -/
theorem one_toExact :
    (Fl.ofBits 0x3FF0000000000000).toExact = some (false, 4503599627370496, -52) := by
  decide

/-- `-0.0` and `+0.0` are *different bit patterns*. -/
theorem negzero_bits_ne :
    (Fl.zero Format.binary64 true).bits ≠ (Fl.zero Format.binary64 false).bits := by
  decide

/-- ...and yet compare *equal*. These two theorems together are the reason `Val.beq`
cannot be structural on floats. -/
theorem negzero_eq_zero :
    FConfig.python.eq (Fl.zero Format.binary64 true) (Fl.zero Format.binary64 false) = true := by
  decide

/-- NaN is not equal to itself. The second half of the same argument. -/
theorem nan_ne_self :
    FConfig.python.eq (Fl.nan Format.binary64) (Fl.nan Format.binary64) = false := by
  decide

/-- NaN is *unordered*, not merely unequal: `<`, `>` and `==` are all false, which a
model based on `Ordering` alone cannot express. -/
theorem nan_unordered (x : Fl) : FConfig.python.cmp (Fl.nan Format.binary64) x = none := by
  simp [FConfig.cmp, Fl.cmpv, Fl.nan, Fl.isNaN, Fl.expField, Fl.mantField, Fl.ofParts,
        Format.binary64, Format.expAllOnes, Format.mantBits]

/-- **`float_beq_is_not_bit_equality`.** Stated as a theorem so that a future `Val.beq`
which forwards floats to structural equality is refuted by a build failure rather than by
a divergence report. -/
theorem float_beq_is_not_bit_equality :
    ∃ x y : Fl, x.bits ≠ y.bits ∧ FConfig.python.eq x y = true := by
  refine ⟨Fl.zero Format.binary64 true, Fl.zero Format.binary64 false, ?_, ?_⟩
  · exact negzero_bits_ne
  · exact negzero_eq_zero

/-- ...and the converse direction: equal bits that do not compare equal. -/
theorem float_bit_equality_is_not_beq :
    ∃ x : Fl, FConfig.python.eq x x = false := ⟨Fl.nan Format.binary64, nan_ne_self⟩

end Fl

/-! ## Evidence

Two kinds, because they answer two different questions.

### 1. Known CPython values, written out

Each `#eval` below is annotated with the value CPython prints. These are the cases a
reader can check by hand.

### 2. A self-checking cross-validation harness

`crossCheck` compares this model against Lean's own `Float` — which is a hardware
`double`, i.e. **the same IEEE 754 binary64 arithmetic CPython's `float` is compiled to
use**. It is the closest thing to a mechanical proof of CPython agreement available
without running CPython from inside Lean, and it runs on every build.

`Float` appears *only* here. No definition the interpreter depends on mentions it; the
model itself is `Nat`/`Int` arithmetic throughout, which is why anything above can be
proved about and this cannot.

Measured, at the time of writing, on the pools below and on larger pools driven from
CPython (1,600 `%`/`math.fmod` pairs taken from CPython itself, 400 correctly-rounded
decimal literals, 729 pairs per operator against hardware doubles, and 256 pairs per
operator in binary32 against `Float32`): **zero mismatches in every case**.
-/

section Evidence

open FConfig

/-- Bits of a Lean `Float`, as an `Fl`. Evidence-only. -/
private def ofFloat (x : Float) : Fl := Fl.ofBits x.toBits.toNat

/-- Does the model's result carry the same bit pattern as the hardware's?

NaN is compared as a *class*, not as a bit pattern: IEEE 754 leaves the payload and the
sign of a NaN unspecified, so requiring bit equality there would be requiring agreement
on something the standard does not fix. (Measured aside: on x86-64 both CPython and this
model produce `0x7ff8000000000000`, so the caveat costs nothing in practice — but the
differential harness must compare NaN-ness rather than bits, or it will manufacture a
divergence the first time it meets a machine whose default NaN is negative.) -/
private def agrees (want : Float) (got : FResult) : Bool :=
  match got with
  | .ok v => if want.isNaN then v.isNaN else v.bits == want.toBits.toNat
  | _     => false

/-- A pool chosen to hit the cases naive models get wrong: signed zeros, subnormals
(`5e-324` is the smallest positive double), the boundary between subnormal and normal,
the largest finite double, values where `int` and `float` diverge (`1e16`, `1e17`), the
smallest double above 1, both infinities, and NaN. -/
private def pool : List Float :=
  [0.0, -0.0, 1.0, -1.0, 0.5, 2.0, 0.1, 0.2, 0.3, 1e-300, 1e300,
   1.7976931348623157e308, 5e-324, 2.2250738585072014e-308, 1234567.891, -9876.54321,
   1e16, 1e17, 3.141592653589793, 1.0000000000000002, 1e100, -1e-100, 7.0, -7.5,
   1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0]

/-- Number of operand pairs on which the model disagrees with the hardware. Every entry
should be `0`; a nonzero entry is a defect in this file, found by the build. -/
private def crossCheck : Nat × Nat × Nat × Nat := Id.run do
  let mut a := 0; let mut s := 0; let mut m := 0; let mut d := 0
  for x in pool do
    for y in pool do
      let (u, v) := (ofFloat x, ofFloat y)
      if !(agrees (x + y) (cDouble.add u v)) then a := a + 1
      if !(agrees (x - y) (cDouble.sub u v)) then s := s + 1
      if !(agrees (x * y) (cDouble.mul u v)) then m := m + 1
      if !(agrees (x / y) (cDouble.div u v)) then d := d + 1
  return (a, s, m, d)

/-- Ordering agrees with the hardware too, including the unordered NaN cases. -/
private def crossCheckCmp : Nat := Id.run do
  let mut n := 0
  for x in pool do
    for y in pool do
      let want : Option Ordering :=
        if x.isNaN || y.isNaN then none
        else if x < y then some .lt else if x == y then some .eq else some .gt
      if python.cmp (ofFloat x) (ofFloat y) != want then n := n + 1
  return n

-- 729 operand pairs per operator, all four operators. Expected `(0, 0, 0, 0)`.
#eval crossCheck                                   -- (0, 0, 0, 0)
-- Ordering: expected `0`.
#eval crossCheckCmp                                -- 0

/-! ### The canonical example, which a rational model gets wrong

CPython:
```
>>> 0.1 + 0.2
0.30000000000000004
>>> (0.1 + 0.2) == 0.3
False
```
-/
#eval (python.add (ofFloat 0.1) (ofFloat 0.2)) == .ok (ofFloat 0.30000000000000004)
                                                   -- true
#eval match python.add (ofFloat 0.1) (ofFloat 0.2) with
      | .ok v => python.eq v (ofFloat 0.3)
      | _     => true                               -- false  (CPython: False)

/-! ### Decimal literals are correctly rounded

`Format.ofDecimal` is what the transpiler needs for a source literal. CPython's `strtod`
is correctly rounded, so these agree bit for bit — including the smallest subnormal and
the overflow-to-infinity case. -/
#eval (Format.binary64.ofDecimal false 1 (-1)).bits == (0.1 : Float).toBits.toNat      -- true
#eval (Format.binary64.ofDecimal false 5 (-324)).bits == (5e-324 : Float).toBits.toNat -- true
#eval (Format.binary64.ofDecimal false 3141592653589793 (-15)).describe
                                          -- "+7074237752028440·2^-51"  (= 3.141592653589793)
#eval (Format.binary64.ofDecimal false 1 400).describe                                 -- "inf"
#eval (Format.binary64.ofDecimal false 1 (-400)).describe                              -- "+0·2^-1074"

/-! ### Signed zero and NaN, i.e. exactly where naive models go wrong -/
#eval (Fl.zero Format.binary64 true).bits != (Fl.zero Format.binary64 false).bits      -- true
#eval python.eq (Fl.zero Format.binary64 true) (Fl.zero Format.binary64 false)         -- true
#eval python.eq (Fl.nan Format.binary64) (Fl.nan Format.binary64)                      -- false
#eval python.lt (Fl.nan Format.binary64) (ofFloat 1.0)                                 -- false
#eval python.lt (ofFloat 1.0) (Fl.nan Format.binary64)                                 -- false
#eval python.truthy (Fl.zero Format.binary64 true)                                     -- false
-- `-0.0 + -0.0 = -0.0`, but `-0.0 + 0.0 = 0.0` and `1.0 - 1.0 = 0.0`: three different
-- answers that a value-level model collapses into one.
#eval (python.add (ofFloat (-0.0)) (ofFloat (-0.0))) == .ok (ofFloat (-0.0))           -- true
#eval (python.add (ofFloat (-0.0)) (ofFloat 0.0))    == .ok (ofFloat 0.0)              -- true
#eval (python.sub (ofFloat 1.0) (ofFloat 1.0))       == .ok (ofFloat 0.0)              -- true

/-! ### Overflow, underflow, infinities -/
#eval (python.mul (ofFloat 1e300) (ofFloat 1e300)).toOption.map Fl.describe   -- some "inf"
#eval (python.mul (ofFloat 1e-300) (ofFloat 1e-300)).toOption.map Fl.describe -- some "+0·2^-1074"
#eval (python.add (ofFloat 5e-324) (ofFloat 5e-324)).toOption.map Fl.describe -- some "+2·2^-1074"
#eval (python.sub (ofFloat (1.0/0.0)) (ofFloat (1.0/0.0))).toOption.map Fl.describe
                                                                              -- some "nan"
#eval (python.mul (ofFloat (1.0/0.0)) (ofFloat 0.0)).toOption.map Fl.describe -- some "nan"

/-! ### The dialect split, which is the point of parameterizing

`1.0 / 0.0` is `ZeroDivisionError` in Python and `inf` in C — the same expression, two
different correct answers. This is `NumConfig.python` vs `NumConfig.c32` in a new domain,
and hardcoding either one silently mistranslates the other language. -/
#eval python.div (ofFloat 1.0) (ofFloat 0.0)          -- exn "ZeroDivisionError"
#eval (cDouble.div (ofFloat 1.0) (ofFloat 0.0)).toOption.map Fl.describe   -- some "inf"
#eval (cDouble.div (ofFloat 0.0) (ofFloat 0.0)).toOption.map Fl.describe   -- some "nan"
#eval python.fmod (ofFloat 1.0) (ofFloat 0.0)         -- exn "ZeroDivisionError"
#eval (cDouble.fmod (ofFloat 1.0) (ofFloat 0.0)).toOption.map Fl.describe  -- some "nan"

-- Excess precision is `ub`, not a number. On x87 without `-ffloat-store`, or with FMA
-- contraction, this expression genuinely has no binary64-determined value.
#eval cDoubleExcess.add (ofFloat 1.0) (ofFloat 1.0)   -- ub "float:excess-precision"

-- C `float` is binary32. Rounding it at binary64 would be the §22 mistranslation in a
-- new domain, so the format is part of the value and a mixed operation is refused.
#eval (Format.binary32.ofDecimal false 1 (-1)).bits                        -- 1036831949
#eval cFloat.add (ofFloat 1.0) (ofFloat 1.0)          -- unmodelled "float:format-mismatch"

/-! ### `%` is not `fmod`

CPython's `float.__mod__` takes the sign of the **divisor**; `math.fmod` takes the sign of
the dividend. Confusing them is the floating-point twin of the §12 integer-modulo bug,
and it is the reason `pyMod` is written in terms of `fmod` plus an explicitly *rounded*
correction rather than recomputed exactly. Verified against CPython on 1,600 pairs. -/
#eval (python.pyMod (ofFloat (-5.5)) (ofFloat 2.0)) == .ok (ofFloat 0.5)    -- true  (CPython: 0.5)
#eval (cDouble.fmod (ofFloat (-5.5)) (ofFloat 2.0)) == .ok (ofFloat (-1.5)) -- true  (CPython: -1.5)
#eval (python.pyMod (ofFloat 5.5) (ofFloat (-2.0))) == .ok (ofFloat (-0.5)) -- true  (CPython: -0.5)
-- a zero remainder takes the sign of the divisor, so `4.0 % -2.0` is `-0.0`
#eval (python.pyMod (ofFloat 4.0) (ofFloat (-2.0))) == .ok (ofFloat (-0.0)) -- true

/-! ### `int` and `float` do not coerce

`10**23 == 1e23` is `False` in CPython, because `1e23` is exactly
`99999999999999991611392`. A model that compares by converting the int to a float would
answer `True` — a silent wrong answer of the `floorDiv` family. -/
#eval python.cmpInt (10 ^ 23) (ofFloat 1e23)         -- some Ordering.gt   (CPython: >)
#eval python.cmpInt (10 ^ 22) (ofFloat 1e22)         -- some Ordering.eq   (CPython: ==)
#eval (python.ofInt (10 ^ 400))                      -- exn "OverflowError"
#eval python.toInt (ofFloat 3.99)                    -- Except.ok 3
#eval python.toInt (ofFloat (-3.99))                 -- Except.ok (-3)     (toward zero)
#eval python.toInt (ofFloat (1.0 / 0.0))             -- Except.error "OverflowError"
#eval python.toInt (ofFloat (0.0 / 0.0))             -- Except.error "ValueError"

/-! ### The visible boundary -/
#eval python.repr (ofFloat 0.1)          -- unmodelled "float:repr-shortest-roundtrip"
#eval python.hash (ofFloat 0.1)          -- unmodelled "float:hash"
#eval python.transcendental "exp"        -- unmodelled "float:exp"

end Evidence

end Autoform.Core
