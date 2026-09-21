import Autoform.Lang.Core.Syntax
import Autoform.Lang.Core.Numeric
import Autoform.Lang.Core.TypedNumeric
import Autoform.Lang.Core.Stdlib

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
instance. `.javascript` mirrors `.python`'s arm: `Dialect.toNumConfig .javascript` is
`NumConfig.python`, whose `divRound` is `.floor`. -/
def Dialect.idiv : Dialect → Int → Int → Int
  | .python,     a, b => Int.fdiv a b
  | .cLike,      a, b => Int.tdiv a b
  | .javascript, a, b => Int.fdiv a b
  | .java,       a, b => Int.tdiv a b
  | .go,         a, b => Int.tdiv a b

/-- Integer remainder under a dialect. See `idiv` — unused, kept exhaustive and
consistent with it. -/
def Dialect.imod : Dialect → Int → Int → Int
  | .python,     a, b => Int.fmod a b
  | .cLike,      a, b => Int.tmod a b
  | .javascript, a, b => Int.fmod a b
  | .java,       a, b => Int.tmod a b
  | .go,         a, b => Int.tmod a b


/-- Result of executing a statement: how control left it and the locals at that point.
Handlers and finalizers run in this environment, including after a return or exception. -/
inductive Ctl where
  | normal    : Env → Ctl
  | ret       : Val → Env → Ctl
  | brk       : Env → Ctl
  | cont      : Env → Ctl
  | exn       : Val → Env → Ctl
  | hole      : String → Ctl
  | outOfFuel : Ctl
  deriving Repr, Inhabited

/-- Locals at a language-level exit. Interpreter failures have no resumable state. -/
def Ctl.env (fallback : Env) : Ctl → Env
  | .normal ρ | .ret _ ρ | .brk ρ | .cont ρ | .exn _ ρ => ρ
  | _ => fallback

/-- Resume a pending exit after a normally completing finalizer, retaining its writes.
The value of a pending return or exception was already evaluated and stays unchanged. -/
def Ctl.withEnv (ρ : Env) : Ctl → Ctl
  | .normal _ => .normal ρ
  | .ret v _ => .ret v ρ
  | .brk _ => .brk ρ
  | .cont _ => .cont ρ
  | .exn v _ => .exn v ρ
  | other => other

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
      | .cLike | .javascript | .java | .go =>
          match (d.toFConfig).ofInt n with
          | .ok x => Fl.cmpv x y
          | _     => none
  | .float x, .int n   =>
      (match d with
       | .python => Fl.cmpIntv n x
       | .cLike | .javascript | .java | .go =>
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
  let op := match op with
    | "py:/" | "js:/" => "/"
    | "js:+" => "+" | "js:-" => "-" | "js:*" => "*" | "js:%" => "%"
    | other => other
  match op with
  | "&&" => .val (.bool (a.truthy && b.truthy))
  | "||" => .val (.bool (a.truthy || b.truthy))
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
                   | _   => if d == .python then fc.pyMod x y else fc.fmod x y)
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
  | _    => match d with
            | .python => .hole s!"numeric:typed-op-in-python:{op}"
            | _       => TypedNumeric.binary op a b

/-- Whether `==`/`!=` on these operands has to consult the heap.

Only a REFERENCE forces it: two distinct objects with equal contents are `==` in Python, and
no structural compare of two refs can see that. The order operators join `==`/`!=` here
because a Python class can define `__lt__` and friends (`cmpDunderTarget`), which needs the
receiver's class off the heap. Everything else stays on `applyBinop`, which is heap-free
and reducible -- the property `Refine.lean` is built on. Named rather than inlined so
proofs can discharge it by `simp` on concrete operands. -/
def isCmpOp (op : String) : Bool :=
  op == "==" || op == "!=" || op == "<" || op == "<=" || op == ">" || op == ">="

def binopNeedsHeap (op : String) (x y : Val) : Bool :=
  isCmpOp op && (x.kind == 8 || y.kind == 8)

@[simp] theorem binopNeedsHeap_int_left (op : String) (i : Int) (y : Val) :
    binopNeedsHeap op (.int i) y = (isCmpOp op && y.kind == 8) := by
  simp [binopNeedsHeap, Val.kind]

@[simp] theorem binopNeedsHeap_arith (x y : Val) (op : String)
    (h : isCmpOp op = false) : binopNeedsHeap op x y = false := by
  simp [binopNeedsHeap, h]

/-- Explicit language operators for newly exported terms. Keeping this dispatch
separate also keeps reduction of the legacy integer operators inexpensive. -/
def languageBinop (d : Dialect) (op : String) (a b : Val) : EResult :=
  match op, a, b with
  -- New exports distinguish Python true division from the legacy floor-division
  -- spelling in previously generated terms. Round the ratio once, including big
  -- integers whose individual conversion to float would overflow.
  | "py:/", .int x, .int y =>
      if y == 0 then .exn (.str "ZeroDivisionError")
      else
        let q := Format.binary64.round (xor (x < 0) (y < 0)) x.natAbs y.natAbs
        if q.isInf then .exn (.str "OverflowError") else .val (.float q)
  | "js:+", .str x, .str y => .val (.str (x ++ y))
  | "js:+", _, _ => match d with
                  | .javascript => flBinop .javascript "+" a b
                  | _           => .hole s!"numeric:js-op-outside-javascript:{op}"
  | "js:-", _, _ => match d with
                  | .javascript => flBinop .javascript "-" a b
                  | _           => .hole s!"numeric:js-op-outside-javascript:{op}"
  | "js:*", _, _ => match d with
                  | .javascript => flBinop .javascript "*" a b
                  | _           => .hole s!"numeric:js-op-outside-javascript:{op}"
  | "js:/", _, _ => match d with
                  | .javascript => flBinop .javascript "/" a b
                  | _           => .hole s!"numeric:js-op-outside-javascript:{op}"
  | "js:%", _, _ => match d with
                  | .javascript => flBinop .javascript "%" a b
                  | _           => .hole s!"numeric:js-op-outside-javascript:{op}"
  | "py:/", _, _ => flBinop .python "/" a b
  | _, _, _ => match d with
               -- Python never reaches a typed operator (the exporter emits none for it,
               -- and their traps name themselves in the family's own terms, not as Python
               -- classes -- see `ExcSafe.lean`). An ORDINARY operator on operands no rule
               -- above covers keeps the `binop:<op>` label it always had, so a `+` on a
               -- builtin-based instance is not misreported as a typed-numeric refusal.
               | .python => if (TypedNumeric.parse op).isSome
                              then .hole s!"numeric:typed-op-in-python:{op}"
                              else .hole s!"binop:{op}"
               | _       => TypedNumeric.binary op a b

/-- Built-in binary operators. Unknown operators are holes, not guesses.

Integer arithmetic goes through `NumConfig`, so width and overflow policy follow the
source dialect: Python gets bignums, C-like gets 32-bit two's-complement. -/
def applyBinop (d : Dialect) (op : String) (a b : Val) : EResult :=
  let nc := d.toNumConfig
  match op, a, b with
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
  | "/",  .int x, .int y => numToE (nc.div x y)
  | "%",  .int x, .int y => numToE (nc.mod x y)
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
  -- under `.cLike` every integer is 32-bit two's-complement, so `1 << 31` is `INT_MIN`
  -- (the wrapping config the oracle measures) and `-1 & 255` is `255`.
  --
  -- `>>` and `>>>` are **two different operators** and the difference is only visible on
  -- a negative left operand: C's `>>` on a signed value is arithmetic (sign-extending) and
  -- on an unsigned value it is logical (zero-filling). Core cannot recover the operand's
  -- signedness at run time — a `Val.int` carries no type — so the *exporter* decides,
  -- from the CPG's static type, which of the two it emits, and holes when the type is
  -- unknown. Collapsing them here would reintroduce exactly the `<operator>.and` mistake
  -- in a place where it is much harder to see.
  | "&",  .int x, .int y => numToE (nc.band x y)
  | "|",  .int x, .int y => numToE (nc.bor x y)
  | "^",  .int x, .int y => numToE (nc.bxor x y)
  | "<<", .int x, .int y => numToE (nc.shl x y)
  | ">>", .int x, .int y => numToE (nc.shr x y)
  | ">>>", .int x, .int y => numToE ({ nc with negRightShift := .logical }.shr x y)
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
  -- `==` on strings compares contents in Python and addresses in C. `Val.beq` is
  -- structural, so it is right for Python and wrong for C.
  -- Java is the third case: strings are values, but `==` is REFERENCE equality, and
  -- Core's one `Val.str` cannot say whether two equal contents are one object.
  | "==", .str _, .str _ =>
      if d.stringEqIsReference then .hole "str:reference-equality"
      else if d.stringsAreValues then .val (.bool (Val.beq a b))
      else .hole "str:pointer-equality-not-modelled"
  | "!=", .str _, .str _ =>
      if d.stringEqIsReference then .hole "str:reference-equality"
      else if d.stringsAreValues then .val (.bool (!Val.beq a b))
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
  | "==", x, y           => .val (.bool (Val.beq x y))
  | "!=", x, y           => .val (.bool (!Val.beq x y))
  -- Reached only when the left operand did not decide the result, so the value
  -- of the expression is the RIGHT operand under value semantics.
  | "&&", _, y           => .val (if d.boolOpsAreValues then y else .bool y.truthy)
  | "||", _, y           => .val (if d.boolOpsAreValues then y else .bool y.truthy)
  | _, _, _              => languageBinop d op a b

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

/-! ### Java and Go, split from `.cLike` (docs/languages.md §5, §6)

Untagged Java arithmetic is `int`: 32-bit and wrapping, like `javac`/HotSpot. Untagged Go
arithmetic is `int`: 64-bit and wrapping. Strings are values in both — `+` concatenates —
and `==` on two strings is content equality in Go but REFERENCE equality in Java, which
Core's one `Val.str` cannot decide, so it is the hole `str:reference-equality` rather than
either wrong answer. Every claim here is a `#guard`, not an oracle: no Java or Go runtime
is compared against yet (the support matrix's last column). -/
example : applyBinop .java "+" (.int 2147483647) (.int 1) = .val (.int (-2147483648)) := by rfl
example : applyBinop .java "*" (.int 100000) (.int 100000) = .val (.int 1410065408) := by rfl
example : applyBinop .go "+" (.int 2147483647) (.int 1) = .val (.int 2147483648) := by rfl
example : applyBinop .go "+" (.int 9223372036854775807) (.int 1) = .val (.int (-9223372036854775808)) := by rfl
example : applyBinop .go "*" (.int 100000) (.int 100000) = .val (.int 10000000000) := by rfl
example : applyBinop .java "+" (.str "a") (.str "b") = .val (.str "ab") := by rfl
example : applyBinop .go "+" (.str "a") (.str "b") = .val (.str "ab") := by rfl
example : applyBinop .java "==" (.str "a") (.str "a") = .hole "str:reference-equality" := by rfl
example : applyBinop .java "!=" (.str "a") (.str "b") = .hole "str:reference-equality" := by rfl
example : applyBinop .go "==" (.str "a") (.str "a") = .val (.bool true) := by rfl
example : applyBinop .cLike "==" (.str "a") (.str "a") = .hole "str:pointer-equality-not-modelled" := by rfl
-- `&&`/`||` yield booleans in both, as in C — the one thing `.cLike` had right for them.
example : applyBinop .java "||" (.int 0) (.int 5) = .val (.bool true) := by rfl
example : applyBinop .go "&&" (.int 1) (.int 0) = .val (.bool false) := by rfl
-- `/` truncates toward zero in both; `-7 / 2` is `-3`.
example : applyBinop .java "/" (.int (-7)) (.int 2) = .val (.int (-3)) := by rfl
example : applyBinop .go "%" (.int (-7)) (.int 3) = .val (.int (-1)) := by rfl

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
    Val.truthy (.float (Fl.zero Format.binary64 true)) = false := by decide

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

/-- Built-in unary operators. -/
def applyUnop (d : Dialect) (op : String) (a : Val) : EResult :=
  match op, a with
  -- Source normalization distinguishes statically invalid raise operands from
  -- strings that might be the current representation of an exception instance.
  -- evalExpr evaluates the operand first, preserving its own errors and effects.
  | "py:raise-invalid", _ =>
      if d == .python then .exn (.str "TypeError") else .hole "raise:wrong-dialect"
  | "py:raise", value =>
      if d == .python then Stdlib.raiseValue value else .hole "raise:wrong-dialect"
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
  | "~", .int x => numToE ((d.toNumConfig).bnot x)
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
  | _, _        =>
      if op.startsWith "py:exception:" then
        if d != .python then .hole "exception:wrong-dialect"
        else match a with
          | .tuple args => Stdlib.makeException (op.drop "py:exception:".length).toString args
          | _ => .hole "exception:argument-shape"
      -- A typed operator carries its own language family and its traps name
      -- themselves in that language's terms (`panic:...`), not as Python exception
      -- classes. The exporter never emits one for a Python file; refusing it here is
      -- what makes `applyUnop_excSafe` a theorem rather than a convention.
      else match d with
        | .python => .hole s!"numeric:typed-op-in-python:{op}"
        | _       => TypedNumeric.unary op a

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

/-- The globals-frame key under which a **class attribute** is stored.

Class bodies are not executed as functions in Core, so a class-level binding like
`__marker = object()` has no frame of its own to live in. It lives in the one globals frame,
under a key no source language can spell: `<classattr>Cache._Cache__marker`. The exporter
writes it from the module-objects initialiser; `applyFunc` reads it for a class-attribute
default and `evalExpr` reads it when `self.<attr>` misses the instance's own fields. One
key format, defined once, so the two readers cannot disagree with the writer. -/
@[simp] def classAttrKey (cls attr : String) : String := "<classattr>" ++ cls ++ "." ++ attr

/-- The base environment of a call: `self` bound if there is a receiver. Named so that a
proof about `applyFunc` has a stable term to case on -- `simp only [applyFunc]` leaves it
folded -- and `@[simp]` so that every proof unfolding `applyFunc` with plain `simp`
reduces it exactly as it reduced the inline `match` this replaces. -/
@[simp] def selfEnv : Option Val → Env
  | some s => [("self", s)]
  | none   => []

/-- Everything the interpreter needs: the callable functions and the source dialect. -/
structure Ctx where
  dialect : Dialect
  table   : FuncTable
  /-- Classes whose base is a builtin type — see `Program.builtinBases`. -/
  builtinBases : List (String × BuiltinBase) := []
  /-- Heap address of the module-level bindings frame. Globals must be mutable and must
  outlive any single call, so they live on the heap rather than in `Env`. -/
  globals : Ref := 0
  /-- `(class, name)` of every `@property` -- see `Program.properties`. Every `Ctx` built
  from a `Program` (`ctxOf`, `runFunc`, `initGlobals`, `runMain`, `ctx_fold`) must pass it
  through, or the contexts disagree and every proof that folds one into the other breaks:
  that disagreement is what a `Ctx` field costs, and it is confined to those sites. -/
  properties : List (String × String) := []

/-- Build a function table from a program. -/
def Program.table (p : Program) : FuncTable := p.funcs.map (fun f => (f.name, f))

/-! ### Name matching the kernel can compute

Every name lookup below used `String.endsWith`/`String.splitOn`. Those are well-founded
recursions over byte positions, and the kernel does not unfold well-founded recursion, so
any proof *by computation* (`decide`, `rfl`, `cbv`) that reached a resolve MISS -- the
suffix scan -- or a class-value's short name did not terminate. Three cachetools
constructors had to be excluded from the generated conformance module for exactly this
reason, and `BuiltinBase.lean` had to state its resolution facts as `#guard`s. The helpers
here do the same work on `List Char`, by structural recursion only: `String.toList` reduces
on a literal, `List.reverse`/`List.isPrefixOf`/`List.take` reduce structurally, so a
concrete lookup now reduces in the kernel. `strEndsWith_eq_endsWith` is the proof that
nothing else changed. -/

/-- `suffix` is a suffix of `s`, decided on the character lists. -/
def strEndsWith (s suffix : String) : Bool := suffix.toList.isSuffixOf s.toList

/-- The structural test agrees with the library's byte-position one. -/
theorem strEndsWith_eq_endsWith (s suffix : String) : strEndsWith s suffix = s.endsWith suffix := by
  unfold strEndsWith String.endsWith
  rw [Bool.eq_iff_iff, List.isSuffixOf_iff_suffix, String.Slice.endsWith_string_iff,
      String.copy_toSlice]

/-- The last dotted segment of a character list; the whole list when there is no dot,
the empty list when the dot is last -- the same answers as `(s.splitOn ".").getLastD s`. -/
def lastDotSegment : List Char → List Char → List Char
  | [],          acc => acc.reverse
  | '.' :: rest, _   => lastDotSegment rest []
  | c :: rest,   acc => lastDotSegment rest (c :: acc)

/-- Everything before the last `.`; empty when there is none -- the same answer as
`".".intercalate (s.splitOn ".").dropLast`. -/
def dropLastDotSegment (cs : List Char) : List Char :=
  match cs.reverse.dropWhile (· != '.') with
  | []          => []
  | _ :: before => before.reverse

-- Agreement with the `splitOn` forms this replaces, on the shapes Joern emits: a file
-- part with dots, the `<meta>` marker, a bare name, a trailing dot.
#guard String.mk (lastDotSegment "cachetools/__init__.py:<module>.Cache".toList []) == "Cache"
#guard String.mk (lastDotSegment "Cache".toList []) == "Cache"
#guard String.mk (lastDotSegment "a.b.".toList []) == ""
#guard String.mk (dropLastDotSegment "d.py:<module>.C.make".toList) == "d.py:<module>.C"
#guard String.mk (dropLastDotSegment "make".toList) == ""
#guard strEndsWith "cnt.py:<module>.Counter.bump" ".Counter.bump" == true
#guard strEndsWith "cnt.py:<module>.Counter.__init__" ".Counter.bump" == false
#guard strEndsWith "x" "" == true
#guard strEndsWith "" ".x" == false

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
    -- it no longer allocates and it exits early on the ambiguous case. The suffix test
    -- is `strEndsWith`, so a concrete miss REDUCES in the kernel (see above).
    let suffix := "." ++ n
    let rec go : FuncTable → Option Func → Option Func
      | [],           acc      => acc
      | (k, f) :: ps, none     => if strEndsWith k suffix then go ps (some f) else go ps none
      | (k, _) :: ps, some f   => if strEndsWith k suffix then none else go ps (some f)
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

/-- Parameters that receive positional arguments, excluding variadic collectors
and recovered Python keyword-only parameters. -/
def Func.posParams (fn : Func) : List String :=
  fn.params.filter fun p => fn.vararg != some p && fn.kwarg != some p &&
    !(fn.pythonSignature.map (fun s => s.keywordOnly.contains p)).getD false

/-- Parameters which can be supplied by name. A positional-only name belongs in
`**kwargs` when that collector exists; it must not overwrite the positional value. -/
def Func.keywordParams (fn : Func) : List String :=
  match fn.pythonSignature with
  | none => fn.posParams
  | some signature => fn.params.filter fun p =>
      fn.vararg != some p && fn.kwarg != some p && !signature.positionalOnly.contains p

/-- The parameters of `fn` that have a literal default, and that default.

Named rather than inlined into `bindParams` so that a caller can state "this function has
no defaults" as a rewritable hypothesis. Proofs about a specific rendered function
discharge it by `rfl`; without a name they would have to rewrite under a `match` on
`pythonSignature`, which `simp` will not do reliably. -/
def Func.literalDefaults (fn : Func) : List (String × DefaultValue) :=
  match fn.pythonSignature with
  | some sig => sig.defaults
  | none     => []

/-- The class-attribute defaults of `fn` (see `PythonSignature.classAttrDefaults`). Named,
like `literalDefaults`, so "this function has none" is one rewritable hypothesis
(`hcad : fn.classAttrDefaults = []`) rather than a `match` on `pythonSignature`. -/
@[simp] def Func.classAttrDefaults (fn : Func) : List (String × String × String) :=
  match fn.pythonSignature with
  | some sig => sig.classAttrDefaults
  | none     => []

/-- Was parameter `p` supplied by this call? Positionally if it is among the first
`vs.length` positional parameters, or by keyword. This is the same reading of a call
`signatureRejected` uses, and it is what "a default applies exactly when the parameter was
not passed" means for a default that cannot be seeded ahead of the arguments. -/
@[simp] def paramSupplied (fn : Func) (p : String) (vs : List Val)
    (kws : List (String × Val)) : Bool :=
  (fn.posParams.take vs.length).contains p || (kws.map Prod.fst).contains p

/-- Seed class-attribute defaults into a base environment, reading each from the globals
frame. Structurally recursive on the list so that `[]` -- every function without such a
default -- reduces to `.inr base` by unfolding alone, with no heap read.

A supplied parameter is skipped: the default is never needed, and resolving it anyway
would let a call that passed every argument hole on a class attribute it never used. A
default that is needed and whose class attribute is not in the globals frame is a hole,
named for the parameter, never a guess -- `unit` here would make `default is self.__marker`
true for a caller who passed `None`, which is a wrong answer where CPython returns the
`None`. -/
@[simp] def seedClassAttrs (ctx : Ctx) (h : Heap) (fn : Func) (base : Env) (vs : List Val)
    (kws : List (String × Val)) : List (String × String × String) → Sum String Env
  | [] => .inr base
  | (p, cls, attr) :: rest =>
      if paramSupplied fn p vs kws then seedClassAttrs ctx h fn base vs kws rest
      else
        match (h.get ctx.globals).bind (fun g => g.fields.find? (·.1 == classAttrKey cls attr)) with
        | some (_, v) => seedClassAttrs ctx h fn (Env.set base p v) vs kws rest
        | none        => .inl s!"default:{p}:class-attr-unresolved"

@[simp] def seedClassAttrDefaults (ctx : Ctx) (h : Heap) (fn : Func) (base : Env)
    (vs : List Val) (kws : List (String × Val)) : Sum String Env :=
  seedClassAttrs ctx h fn base vs kws fn.classAttrDefaults

/-- Bind a call's arguments into the callee's environment.

Argument validation happens in `applyFunc` and `applyClosure` before execution.
This helper constructs the environment for a valid call:

* positional arguments fill `posParams` left to right;
* leftovers go to `vararg` as a `tuple` — an empty one when there are none, which is
  why `def f(*a)` called with no arguments binds `a` to `()` rather than to `unit`;
* a keyword argument naming a keyword-capable parameter binds that parameter;
* every other keyword argument goes to `kwarg` as a `dict` with `str` keys.

Surplus positional arguments and unexpected keywords are rejected by the callers.
Recovered Python signatures also reject missing required parameters and duplicate
bindings. Default values remain unsupported by source translation. Functions with
legacy metadata (`pythonSignature = none`) retain their historical binding behavior;
this helper alone is not a Python call validator. -/
def bindParams (fn : Func) (base : Env) (vs : List Val)
    (kws : List (String × Val)) : Env :=
  -- Literal defaults are seeded FIRST, so any argument actually supplied overwrites
  -- them. Ordering it this way keeps the rule "a default applies exactly when the
  -- parameter was not passed" without needing to ask whether each name is already
  -- bound. For a function with no defaults the list is empty and this `foldl` reduces
  -- to `base`, so every previously rendered corpus keeps the term it had.
  let base  := fn.literalDefaults.foldl
                  (fun (e : Env) (d : String × DefaultValue) => Env.set e d.1 d.2.toVal) base
  let ps    := fn.posParams
  let ρ₀    := (ps.zip vs).foldl (fun (e : Env) (x, v) => Env.set e x v) base
  let rest  := vs.drop ps.length
  let ρ₁    := match fn.vararg with
               | some a => Env.set ρ₀ a (.tuple rest)
               | none   => ρ₀
  let named := kws.filter (fun kv => fn.keywordParams.contains kv.1)
  let extra := kws.filter (fun kv => !fn.keywordParams.contains kv.1)
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

This check rejects only a surplus. `signatureRejected` separately checks missing
required parameters when Python signature metadata is present. Legacy functions
without that metadata cannot distinguish required parameters from defaults.

A `*args` parameter absorbs any surplus, so a callee with `vararg` is never rejected. -/
def posRejected (fn : Func) (vs : List Val) : Bool :=
  fn.vararg.isNone && fn.posParams.length < vs.length

/-- A call passing no more arguments than the callee has positional parameters is never
rejected — in particular the zero-argument call, which is what most callers in a rendered
corpus are. -/
@[simp] theorem posRejected_nil (fn : Func) : posRejected fn [] = false := by
  simp [posRejected]

/-- `posRejected` on the shape a rendered corpus actually presents: a `Func` literal with
both variadic fields at their `none` defaults. The companion of `bindParams_mk`, and
needed for the same reason — a proof about a literal `Func` cannot fire a hypothesis-form
lemma without first deciding which `fn` it is about. -/
@[simp] theorem posRejected_mk (name : String) (params : List String) (body : Stmt)
    (vs : List Val) :
    posRejected ⟨name, params, body, none, none, none⟩ vs
      = decide (params.length < vs.length) := by
  have : (List.filter (fun p => none != some p) params) = params := by
    simp [List.filter_eq_self]
  simp [posRejected, Func.posParams, this]

/-- Does this call pass a keyword argument the callee cannot accept? CPython raises
`TypeError: f() got an unexpected keyword argument 'k'`; `bindParams` alone would silently
drop it, which is the silently-wrong shape this project keeps catching, so the check is
separate and `applyFunc` turns it into the exception. -/
def kwargsRejected (fn : Func) (kws : List (String × Val)) : Bool :=
  (fn.kwarg.isNone && kws.any (fun kv => !fn.keywordParams.contains kv.1)) ||
  -- `def f(self, **kw)` called as `o.f(self=1)`: the bound receiver already fills `self`,
  -- and CPython raises `TypeError: got multiple values for argument 'self'`. The exporter
  -- stripped `self` from `params`, so without this the keyword would land in `**kw`
  -- silently -- see `PythonSignature.receiverName`.
  (match fn.pythonSignature with
   | some sig => match sig.receiverName with
                 | some r => kws.any (fun kv => kv.1 == r)
                 | none   => false
   | none => false)

/-- A call with no keyword arguments can never be rejected. -/
@[simp] theorem kwargsRejected_nil (fn : Func) : kwargsRejected fn [] = false := by
  unfold kwargsRejected
  simp only [List.any_nil, Bool.and_false, Bool.false_or]
  split <;> (try split) <;> rfl

/-- Validate already evaluated arguments against a recovered Python signature.
Captured locals cannot supply missing parameters. Positional-only keywords may
enter `**kwargs`, but cannot satisfy a required positional-only parameter.
Duplicate keyword expansion must also be checked during argument evaluation to
preserve the timing of an error relative to later argument effects. -/
def signatureRejected (fn : Func) (vs : List Val) (kws : List (String × Val)) : Bool :=
  match fn.pythonSignature with
  | none => false
  | some signature =>
      let positional := fn.posParams.take vs.length
      let named := (kws.map Prod.fst).filter fn.keywordParams.contains
      signature.required.any (fun p => !(positional ++ named).contains p) ||
        named.any positional.contains ||
        decide ((kws.map Prod.fst).eraseDups.length < kws.length)

@[simp] theorem signatureRejected_legacy (name : String) (params : List String)
    (body : Stmt) (vararg kwarg : Option String) (vs : List Val) (kws : List (String × Val)) :
    signatureRejected ⟨name, params, body, vararg, kwarg, none⟩ vs kws = false := rfl

/-- A function with no variadic parameters, called with no keyword arguments, binds
exactly what `applyFunc` bound before the calling convention existed. This is the
compatibility equation: every corpus rendered before starred arguments were modelled has
`vararg = none` and `kwarg = none`, so nothing about it changed. -/
theorem bindParams_plain {fn : Func} (base : Env) (vs : List Val)
    (h1 : fn.vararg = none) (h2 : fn.kwarg = none) (h3 : fn.pythonSignature = none) :
    bindParams fn base vs [] =
      (fn.params.zip vs).foldl (fun (e : Env) (x, v) => Env.set e x v) base := by
  have : (List.filter (fun p => none != some p) fn.params) = fn.params := by
    simp [List.filter_eq_self]
  simp [bindParams, Func.literalDefaults, Func.posParams, Func.keywordParams, h1, h2, h3, this]

/-- The same equation in the shape a rendered corpus actually presents: a `Func` literal
with both variadic fields at their `none` defaults. Stated separately because the
hypothesis form of `bindParams_plain` cannot fire on a literal without first deciding
which `fn` it is about. -/
@[simp] theorem bindParams_mk (name : String) (params : List String) (body : Stmt)
    (base : Env) (vs : List Val) :
    bindParams ⟨name, params, body, none, none, none⟩ base vs [] =
      (params.zip vs).foldl (fun (e : Env) (x, v) => Env.set e x v) base :=
  bindParams_plain base vs rfl rfl rfl

/-- The short class name behind a class VALUE.

The exporter marks a class value by suffixing `<meta>` to the qualified name, and
`resolveMethod`/`classDefines` want the short name -- the last dotted segment. This cannot
split the whole name, because the FILE part contains dots
(`cachetools/__init__.py:<module>.Cache<meta>`). Named rather than inlined so that proofs
about the `mcall` case have a term to talk about. -/
def classNameOfValue (g : String) : String :=
  -- Structural on the character list (`lastDotSegment`), for the same reason as
  -- `strEndsWith`: this runs on every method call through a class value, and a proof by
  -- computation that reaches it must be able to unfold it.
  let cs := g.toList
  let base := if strEndsWith g "<meta>" then (cs.reverse.drop 6).reverse else cs
  String.mk (lastDotSegment base [])

/-- A `@classmethod`: the recovered signature says the receiver is the class. -/
def Func.isClassMethod (fn : Func) : Bool :=
  fn.pythonSignature.bind (·.receiverKind) == some "class"

/-- The class VALUE that owns a method, rebuilt from the method's qualified name.

A classmethod reached through an INSTANCE (`c.make(3)`) still receives the class, and the
instance's `Obj` only carries the short class name. The method's own name carries the
qualified one -- `d.py:<module>.C.make` -- so dropping its last dotted segment and adding
the exporter's `<meta>` marker gives exactly the value `typeValue` emits for `C`. Splitting
on `.` is safe here because the file part's dots are never the LAST segment. -/
def Func.ownerClassValue (fn : Func) : Val :=
  .fn (String.mk (dropLastDotSegment fn.name.toList) ++ "<meta>")

/-- Resolve a method on a class: prefer `Cls.meth`, else any `.meth`. -/
def Ctx.resolveMethod (ctx : Ctx) (cls meth : String) : Option Func :=
  match ctx.table.filter (fun p => strEndsWith p.1 ("." ++ cls ++ "." ++ meth)) with
  | (_, f) :: _ => some f
  | []          => ctx.resolve meth

/-- Does this class define this method *itself*? Unlike `resolveMethod` there is no
free-function fallback, so a global `__eq__` cannot be mistaken for a class's own. -/
def Ctx.classDefines (ctx : Ctx) (cls meth : String) : Bool :=
  ctx.table.any (fun p => strEndsWith p.1 ("." ++ cls ++ "." ++ meth))

/-- The user-class method a container operation on an ORDINARY instance dispatches to.

`x in c`, `c[k]`, `c[k] = v` and `del c[k]` on an instance are `c.__contains__(x)`,
`c.__getitem__(k)`, `c.__setitem__(k, v)` and `c.__delitem__(k)` in Python. This is
`some (r, fn)` exactly when `c` is a reference to an ordinary instance -- payload `.none`,
so a boxed container keeps its structural path -- whose class DEFINES the method itself
(`classDefines`, so a free function that happens to be called `__getitem__` is not
mistaken for it), under `.python`. Everything else is `none` and the caller falls back to
the structural behaviour, including the hole it had before. The `Func` is the one
`resolveMethod` finds, which is what `FuelMono`'s context hypothesis is stated over. -/
def Ctx.dunderOn (ctx : Ctx) (h : Heap) (c : Val) (name : String) : Option (Ref × Func) :=
  match c with
  | .ref r =>
      if ctx.dialect == .python then
        match h.get r with
        | some o =>
            match o.payload with
            | .none =>
                if ctx.classDefines o.cls name then
                  match ctx.resolveMethod o.cls name with
                  | some fn => some (r, fn)
                  | none    => none
                else none
            | _ => none
        | none => none
      else none
  | _ => none

/-- A dispatched dunder is a resolved method, so `FuelMono`'s and `ExcSafe`'s hypotheses
about `resolveMethod` cover it. -/
theorem Ctx.dunderOn_resolves {ctx : Ctx} {h : Heap} {c : Val} {name : String} {r : Ref}
    {fn : Func} (hd : ctx.dunderOn h c name = some (r, fn)) :
    ∃ cls, ctx.resolveMethod cls name = some fn := by
  unfold Ctx.dunderOn at hd
  repeat' split at hd
  all_goals first | (cases hd; exact ⟨_, by assumption⟩) | cases hd

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

/-- Construct an instance of a class whose base is a builtin type: `X(iterable)` for
`class X(tuple)` / `class X(list)`, `X(d)` for `class X(dict)`, `X(s)` for
`class X(str)`, and `X()` for the empty instance.

Deliberately **refuses** two shapes rather than approximating them:

* a class that defines its own `__init__` — Core would have to run it against a value
  that has no mutable attributes, so whatever it did would be lost;
* a class that defines its own `__eq__` — `Val.beq` compares `bobj`s by contents and
  has no dunder dispatch, so an overridden `__eq__` would be silently ignored. That is
  precisely the silent-wrong outcome this representation is supposed to avoid, so it is
  a hole instead.

Both refusals are *holes*, i.e. counted ignorance, not wrong answers. -/
def allocBuiltin (ctx : Ctx) (cls : String) (b : BuiltinBase) (vs : List Val) : EResult :=
  if ctx.classDefines cls "__init__" then .hole s!"alloc:builtin-base:{cls}:own-__init__"
  else if ctx.classDefines cls "__eq__" then .hole s!"alloc:builtin-base:{cls}:own-__eq__"
  else
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

/-- A JavaScript property read on a boxed container. An object literal's own keys are
its properties (`{a: 1}.a`), an array's `length` is its element count, and any other
name is `undefined` -- never an exception, which is what makes `jsContainerField_ne_exn`
in `ExcSafe.lean` one line. `.none` is unreachable from the caller (it is gated on
`Payload.toVal.isSome`) and stays a hole so the gate can never be quietly weakened. -/
def jsContainerField (p : Payload) (f : String) : EResult :=
  match p with
  | .list vs  => if f == "length" then .val (.int vs.length) else .val .unit
  | .dict kvs => match Stdlib.dictGet kvs (.str f) with
                 | some v => .val v
                 | none   => .val .unit
  | .tuple _  => .val .unit
  | .none     => .hole s!"field:{f}:on-container"

/-- What a Python `raise e` does with the value `e` evaluated to.

Two kinds of value reach `Stmt.raise` from the exporter, and they must be told apart:

* a value produced by the `py:exception:<Name>` constructor operator, or an
  already-caught exception being re-raised. In Core's encoding an exception IS the `.str`
  naming its class, so such a value is `.str name` with `name ∈ Stdlib.excNames`, and
  raising it means raising exactly that -- `.exn v`;
* anything else, which `Stdlib.raiseValue` classifies: a builtin class reference
  instantiates, a string that is not an exception name is a `TypeError` as in CPython,
  and an object Core cannot model holes.

`raiseValue` deliberately holes on a `.str` that IS an exception name ("ambiguous"): at
a dynamic `raise <expr>` site, which the exporter routes through the `py:raise` unop, a
bare string equal to `"ValueError"` cannot be told from the exception. At `Stmt.raise`
the exporter has already made that distinction -- it emits this statement only on the
constructor path and the re-raise path -- so the represented-name case short-circuits
before `raiseValue` would call it ambiguous. The two paths are separated by the
EXPORTER; the value alone cannot separate them, and this comment is where that lives.

Either way every exception this produces names a represented class
(`pythonRaise_excSafe`, `Autoform/Lang/Core/ExcSafe.lean`), which is the invariant that
lets the try/except lowering drop `control:TRY-exception-representation`. -/
def pythonRaise (v : Val) : EResult :=
  match v with
  | .str name => if Stdlib.excNames.contains name then .exn v else Stdlib.raiseValue v
  | _         => Stdlib.raiseValue v

/-! ## Value dunders on ordinary instances

Python lets a class redefine what a VALUE means for its instances: `a == b` is
`a.__eq__(b)`, `a < b` is `a.__lt__(b)`, `len(a)` is `a.__len__()`, `bool(a)` is
`a.__bool__()` (or, failing that, `a.__len__() != 0`), `hash`/`str`/`repr` likewise. Core
answered all of these structurally -- identity for `==`, a hole for `<`, a hole for `len`
-- which for a class that defines the dunder is a silent wrong answer, not a gap. The two
helpers below decide WHETHER a dunder applies; the interpreter makes the call, so fuel
monotonicity and exception safety go through the ordinary `applyFunc` induction.

Both are gated on `.python` and on the receiver being an ordinary instance -- a heap
object with no container payload (a boxed list compares by contents, `Val.eqPy`) and not
a module frame -- whose class DEFINES the method itself (`Ctx.classDefines`, not
`resolveMethod`, so a free function named `__eq__` cannot be mistaken for a method).
Only the LEFT operand dispatches; CPython's reflected `__gt__`-for-`<` fallback when
`__lt__` returns `NotImplemented` is not modelled, and `NotImplemented` has no value here. -/

/-- The dunder a comparison operator names. `!=` is resolved by `cmpDunderTarget`
(`__ne__`, else the negation of `__eq__`, as CPython's default `__ne__` does). -/
@[simp] def cmpDunderName : String → Option String
  | "==" => some "__eq__"
  | "<"  => some "__lt__"
  | "<=" => some "__le__"
  | ">"  => some "__gt__"
  | ">=" => some "__ge__"
  | _    => none

/-- `(receiver, class, method, negate)` when `x op y` dispatches to a dunder on `x`;
`none` means "compare structurally, as before". -/
@[simp] def cmpDunderTarget (ctx : Ctx) (h : Heap) (op : String) (x : Val) :
    Option (Ref × String × String × Bool) :=
  if ctx.dialect != .python then none else
  match x with
  | .ref r =>
    match h.get r with
    | some o =>
      if o.payload.toVal.isSome || o.cls.startsWith "<module>" then none
      else if op == "!=" then
        if ctx.classDefines o.cls "__ne__" then some (r, o.cls, "__ne__", false)
        else if ctx.classDefines o.cls "__eq__" then some (r, o.cls, "__eq__", true)
        else none
      else
        match cmpDunderName op with
        | some m => if ctx.classDefines o.cls m then some (r, o.cls, m, false) else none
        | none   => none
    | none => none
  | _ => none

/-- `(receiver, class, method)` when the builtin `f` applied to exactly one ordinary
instance dispatches to that instance's class. `bool` falls back to `__len__` as CPython
does; everything else names exactly one method. -/
@[simp] def builtinDunderTarget (ctx : Ctx) (h : Heap) (f : String) (vs : List Val) :
    Option (Ref × String × String) :=
  if ctx.dialect != .python then none else
  match vs with
  | [.ref r] =>
    match h.get r with
    | some o =>
      if o.payload.toVal.isSome || o.cls.startsWith "<module>" then none else
      let pick (m : String) : Option (Ref × String × String) :=
        if ctx.classDefines o.cls m then some (r, o.cls, m) else none
      match f with
      | "len"  => pick "__len__"
      | "hash" => pick "__hash__"
      | "str"  => pick "__str__"
      | "repr" => pick "__repr__"
      | "bool" => match pick "__bool__" with
                  | some t => some t
                  | none   => pick "__len__"
      | _      => none
    | none => none
  | _ => none

/-- What the builtin makes of the dunder's answer. CPython type-checks it: `__len__` must
return a non-negative `int`, `__hash__` an `int`, `__str__`/`__repr__` a `str`,
`__bool__` a `bool`; and `bool()` through `__len__` is the length's truthiness. -/
@[simp] def builtinDunderResult (f m : String) (v : Val) : EResult :=
  match f, v with
  | "len",  .int i  => if i < 0 then .exn (.str "ValueError") else .val v
  | "len",  _       => .exn (.str "TypeError")
  | "hash", .int _  => .val v
  | "hash", _       => .exn (.str "TypeError")
  | "str",  .str _  => .val v
  | "str",  _       => .exn (.str "TypeError")
  | "repr", .str _  => .val v
  | "repr", _       => .exn (.str "TypeError")
  | "bool", .bool _ => if m == "__len__" then .exn (.str "TypeError") else .val v
  | "bool", .int i  => if m == "__len__" then .val (.bool (i != 0)) else .exn (.str "TypeError")
  | "bool", _       => .exn (.str "TypeError")
  | _, _            => .val v

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
        match h.get ctx.globals with
        | some g =>
          match g.fields.find? (·.1 == x) with
          | some (_, v) => (h, .val v)
          | none        => match ctx.resolve x with
                           | some _ => (h, .val (.fn x))
                           | none   => (h, .val .unit)
        | none => match ctx.resolve x with
                  | some _ => (h, .val (.fn x))
                  | none   => (h, .val .unit)
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
      | (h₁, .val v) => (h₁, applyUnop ctx.dialect op v)
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
        if op == "&&" && !x.truthy then
          (h₁, .val (if ctx.dialect.boolOpsAreValues then x else .bool false))
        else if op == "||" && x.truthy then
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
              -- A comparison whose LEFT operand is an ordinary instance of a class that
              -- defines the dunder RUNS it (`cmpDunderTarget`); `!=` through `__eq__`
              -- negates the truthiness of what `__eq__` returned.
              match cmpDunderTarget ctx h₂ op x with
              | some (r, cls, m, neg) =>
                match ctx.resolveMethod cls m with
                | some fn =>
                  match applyFunc ctx n h₂ fn (some (.ref r)) [y] [] with
                  | (h₃, .val v) => (h₃, .val (if neg then .bool (!v.truthy) else v))
                  | (h₃, e)      => (h₃, e)
                | none => (h₂, .hole s!"binop:{op}:dunder-unresolved")
              | none =>
                if op == "==" || op == "!=" then
                  match Val.eqPy h₂ (Val.eqFuel h₂) x y with
                  | some r => (h₂, .val (.bool (if op == "==" then r else !r)))
                  | none   => (h₂, .outOfFuel)
                else (h₂, applyBinop ctx.dialect op x y)
            else (h₂, applyBinop ctx.dialect op x y)
          | (h₂, r)      => (h₂, r)
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .cond c t e =>
      match evalExpr ctx n h ρ c with
      | (h₁, .val v) => if v.truthy then evalExpr ctx n h₁ ρ t else evalExpr ctx n h₁ ρ e
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
            -- An ordinary instance whose class defines `__contains__`: `x in c` IS
            -- `c.__contains__(x)`, and `not in` negates its truthiness -- CPython's
            -- protocol. Boxed containers, builtin-based instances and immediates take
            -- the structural path below; `.unbox` is what reads a boxed list or dict.
            match ctx.dunderOn h₂ c "__contains__" with
            | some (r, fn) =>
                match applyFunc ctx n h₂ fn (some (.ref r)) [x] [] with
                | (h₃, .val rv) => (h₃, .val (.bool (if neg then !rv.truthy else rv.truthy)))
                | (h₃, res)     => (h₃, res)
            | none =>
            match valIn x (c.unbox h₂) with
            | .val (.bool r) => (h₂, .val (.bool (if neg then !r else r)))
            | r              => (h₂, r)
        | (h₂, r) => (h₂, r)
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .index a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val c) =>
        match evalExpr ctx n h₁ ρ b with
        | (h₂, .val k) =>
          -- An ordinary instance whose class defines `__getitem__`: `c[k]` IS
          -- `c.__getitem__(k)`. Checked first because the structural match below
          -- cannot see a user class; boxed containers are `none` here and unaffected.
          match ctx.dunderOn h₂ c "__getitem__" with
          | some (r, fn) => applyFunc ctx n h₂ fn (some (.ref r)) [k] []
          | none =>
          -- `A((0,))[0]` is `0` in CPython for `class A(tuple)`.
          -- `.unbox` is the boxed-container case: after the switchover `xs[0]` reads
          -- through a `Val.ref`, and without it a subscript of a list literal holes.
          match (c.unbox h₂).unbuiltin, k with
          | .list vs, .int i | .tuple vs, .int i =>
              -- Python indexes relative to the end for negative integers.
              -- Check the signed bound before toNat, which otherwise clamps a
              -- negative index to zero and can make incorrect mutants survive.
              let j := if ctx.dialect == .python && i < 0 then i + (vs.length : Int) else i
              -- Out of range: Python raises, JavaScript answers `undefined`. Neither is
              -- a hole -- both are values the language defines.
              let outOfRange : EResult :=
                if ctx.dialect == .javascript then .val .unit else .exn (.str "IndexError")
              if j < 0 then (h₂, outOfRange)
              else if hh : j.toNat < vs.length then (h₂, .val (vs[j.toNat]))
              else (h₂, outOfRange)
          -- JavaScript strings index by UTF-16 code unit. A hit is the one-unit string;
          -- out of range is `undefined`; a lone surrogate has no `Char` and is refused
          -- rather than replaced with `'\0'`. Python's `s[i]` keeps the hole it has:
          -- codepoint indexing with `IndexError` is a separate piece of work.
          | .str s, .int i =>
              if ctx.dialect == .javascript then
                match s.utf16At i with
                | none   => (h₂, .val .unit)
                | some u =>
                    if u.isUTF16Surrogate then (h₂, .hole "index:js-lone-surrogate")
                    else (h₂, .val (.str (String.singleton (Char.ofNat u))))
              else (h₂, .hole "index:unsupported")
          | .dict kvs, key =>
              match kvs.find? (fun kv => Val.beq kv.1 key) with
              | some (_, v) => (h₂, .val v)
              | none        => (h₂, .exn (.str "KeyError"))
          | _, _ => (h₂, .hole "index:unsupported")
        | (h₂, r) => (h₂, r)
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .slice a lo hi st =>
      -- `xs[lo:hi:st]` (`docs/boxed-containers.md` §9 item 3, now landed). Order is
      -- receiver, lower, upper, step -- CPython's. A bound is an `Int`, or `unit` for
      -- Python's `None` (the default for the step's direction); anything else is a
      -- `TypeError`, and a zero step a `ValueError`, both as CPython reports them.
      --
      -- A slice is a NEW container. For a boxed list receiver that means a fresh boxed
      -- list -- `ys = xs[:]` is the idiom for a copy precisely because it does not
      -- alias -- gated on the dialect like every other allocation. A tuple slice is a
      -- tuple value and a string slice a string; both are immutable in Python and need
      -- no identity. `d[1:2]` on a dict is Python's "unhashable type: 'slice'".
      match evalExpr ctx n h ρ a with
      | (h₁, .val c) =>
        match evalExpr ctx n h₁ ρ lo with
        | (h₂, .val lv) =>
          match evalExpr ctx n h₂ ρ hi with
          | (h₃, .val hv) =>
            match evalExpr ctx n h₃ ρ st with
            | (h₄, .val sv) =>
              match Stdlib.sliceBound lv, Stdlib.sliceBound hv, Stdlib.sliceBound sv with
              | some lo', some hi', some st' =>
                match (c.unbox h₄).unbuiltin with
                | .list vs =>
                    match Stdlib.sliceIndices vs.length lo' hi' st' with
                    | none    => (h₄, .exn (.str "ValueError"))
                    | some ks =>
                        let picked := Stdlib.slicePick vs ks
                        if ctx.dialect == .python then
                          let (h₅, r) := h₄.alloc { cls := "list", fields := [], payload := .list picked }
                          (h₅, .val (.ref r))
                        else (h₄, .val (.list picked))
                | .tuple vs =>
                    match Stdlib.sliceIndices vs.length lo' hi' st' with
                    | none    => (h₄, .exn (.str "ValueError"))
                    | some ks => (h₄, .val (.tuple (Stdlib.slicePick vs ks)))
                | .str s =>
                    let cs := s.toList
                    match Stdlib.sliceIndices cs.length lo' hi' st' with
                    | none    => (h₄, .exn (.str "ValueError"))
                    | some ks => (h₄, .val (.str (String.mk (ks.filterMap (cs[·]?)))))
                | .dict _ => (h₄, .exn (.str "TypeError"))
                | _       => (h₄, .hole "slice:unsupported")
              | _, _, _ => (h₄, .exn (.str "TypeError"))
            | (h₄, r) => (h₄, r)
          | (h₃, r) => (h₃, r)
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
                           -- that no `class` statement in any language can spell — is
                           -- Python's module namespace as an object: Language Reference
                           -- §3.2.9 (Modules), "attribute references are translated to
                           -- lookups in this dictionary, e.g. `m.x` is equivalent to
                           -- `m.__dict__["x"]`". Its fields are its top-level functions,
                           -- classes and submodules (written by `<module-objects>`) AND
                           -- its module-level variables, written by the module's own body
                           -- as each binding runs (§5.4.1: the body executes in that
                           -- namespace) -- so the value is the one the body computed, not
                           -- a pre-capture. A name the body never bound is, in CPython,
                           -- an `AttributeError`; answering `unit` for it is the silent
                           -- wrong answer, naming the miss is the honest one. Ordinary
                           -- objects keep the documented `unit` behaviour.
                           | none        =>
                             if o.cls.startsWith "<module>" then
                               (h₁, .hole s!"module-attr:{f}")
                             -- A boxed container has no `__dict__` to miss into:
                             -- `{'a': 1}.a` is an AttributeError in Python and was a hole
                             -- before boxing. Answering `unit` would let the commit that
                             -- boxes containers introduce a silent wrong answer while
                             -- removing others. Gated on the dialect because only Python
                             -- boxes, so no `.cLike` corpus can reach a payload and none
                             -- of their specs need to say so.
                             -- JavaScript: a property read on a boxed container is
                             -- answered on the field path -- `xs.length` on an array, a
                             -- key on an object literal (`{a: 1}.a`), `undefined` for
                             -- anything else. `jsContainerField` is the whole table.
                             else if ctx.dialect == .javascript && o.payload.toVal.isSome then
                               (h₁, jsContainerField o.payload f)
                             else if ctx.dialect.boxesContainers && o.payload.toVal.isSome then
                               (h₁, .hole s!"field:{f}:on-container")
                             -- A `@property`: the attribute read IS a call, so run the
                             -- getter on the receiver. Keyed by `(o.cls, f)` against
                             -- `ctx.properties`, and consulted only after the ordinary
                             -- field and capture lookups have missed -- Python's own
                             -- order, so an instance attribute shadowing a property is
                             -- not this case. Python only: a property is a Python
                             -- construct, and the gate is what keeps every `.cLike`
                             -- corpus, and every accessor theorem about one, untouched.
                             else if ctx.dialect == .python &&
                                     ctx.properties.any (fun p => p.1 == o.cls && p.2 == f) then
                               match ctx.resolveMethod o.cls f with
                               | some fn => applyFunc ctx n h₁ fn (some (.ref r)) [] []
                               | none    => (h₁, .hole s!"property:{f}:unresolved")
                             -- A CLASS attribute read through an instance: `self.__marker`
                             -- where `__marker = object()` was bound in the class body.
                             -- Python's lookup falls from the instance to its class, and
                             -- that is the fallback here -- to the globals-frame key the
                             -- module initialiser wrote (`classAttrKey`). Python-only,
                             -- because only Python has class bodies and because that is
                             -- what keeps every `.cLike` accessor theorem out of the side
                             -- condition this adds. Not recursive, so fuel-monotonicity of
                             -- `.field` is unchanged. A miss stays the documented `unit`
                             -- (docs/languages.md §13 prices changing that separately).
                             else if ctx.dialect == .python then
                               match (h₁.get ctx.globals).bind
                                       (fun g => g.fields.find? (·.1 == classAttrKey o.cls f)) with
                               | some (_, v) => (h₁, .val v)
                               | none        => (h₁, .val .unit)
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
      -- JavaScript: `s.length` is the number of UTF-16 code units, not codepoints.
      | (h₁, .val (.str s)) =>
          if ctx.dialect == .javascript && f == "length" then (h₁, .val (.int s.jsLength))
          else (h₁, .hole s!"field:{f}:non-object")
      | (h₁, .val _)        => (h₁, .hole s!"field:{f}:non-object")
      | (h₁, r)             => (h₁, r)
  -- `[*a, b]` and `(*a, b)` splice, exactly as in a call. `{**d}` has no display form
  -- here (a dict display is `dictE`), so a keyword group in a list/tuple literal is a
  -- shape we do not model and it says so.
  | n+1, h, ρ, .listE es =>
      match evalList ctx n h ρ es with
      -- THE SWITCHOVER. A Python or JavaScript list literal allocates: both languages'
      -- arrays are objects with identity. NOT C -- an aggregate initializer is a value,
      -- has no identity to share, and `Dialect.fieldsOnDicts` reads it by field name, so
      -- boxing it would make C wrong in the commit that makes Python right. The dialect
      -- predicate `boxesContainers` is where that line is drawn.
      | (h₁, .inr (vs, []))  =>
          if ctx.dialect.boxesContainers then
            let (h₂, r) := h₁.alloc { cls := "list", fields := [], payload := .list vs }
            (h₂, .val (.ref r))
          else (h₁, .val (.list vs))
      | (h₁, .inr (_,  _))   => (h₁, .hole "op:keyword-in-literal")
      | (h₁, .inl r)         => (h₁, r)
  | n+1, h, ρ, .tupleE es =>
      match evalList ctx n h ρ es with
      | (h₁, .inr (vs, []))  => (h₁, .val (.tuple vs))
      | (h₁, .inr (_,  _))   => (h₁, .hole "op:keyword-in-literal")
      | (h₁, .inl r)         => (h₁, r)
  | n+1, h, ρ, .dictE kvs =>
      match evalPairs ctx n h ρ kvs with
      | (h₁, .inr ps) =>
          if ctx.dialect.boxesContainers then
            let (h₂, r) := h₁.alloc { cls := "dict", fields := [], payload := .dict ps }
            (h₂, .val (.ref r))
          else (h₁, .val (.dict ps))
      | (h₁, .inl r)  => (h₁, r)
  | n+1, h, ρ, .call f args =>
      match evalList ctx n h ρ args with
      | (h₁, .inl r)  => (h₁, r)
      | (h₁, .inr (vs, kws)) =>
        match ctx.resolve f with
        | some fn =>
            -- A `@classmethod` called through its qualified name (`C.make(3)` lowered to a
            -- direct call) is still bound to its class: CPython passes `cls` whether the
            -- call goes through the class or an instance, so the class value goes in as
            -- the first positional here exactly as it does at the `.mcall` sites.
            if fn.isClassMethod then applyFunc ctx n h₁ fn none (fn.ownerClassValue :: vs) kws
            else applyFunc ctx n h₁ fn none vs kws
        | none    =>
          -- Not a statically known function: it may be a function value or closure held
          -- in a variable (`f = g; f(x)`, decorators, callbacks).
          match ρ.get f with
          | .fn g      => match ctx.resolve g with
                          | some fn =>
                            -- An unbound method reached through a VARIABLE -- a decorator's
                            -- wrapped function, a callback, `cache_getitem = Cache.__getitem__`
                            -- -- receives its receiver as the first POSITIONAL argument. That
                            -- is what `self` is in Python; the receiver is only implicit at a
                            -- `.`-call. `applyFunc` binds the receiver separately, so the head
                            -- has to be split off here, or it lands on `self`'s successor and
                            -- the call reports a spurious arity `TypeError`.
                            -- A `@classmethod` used as a VALUE (`f = C.make; f(3)`) is
                            -- already bound to its class in Python, so the class is the
                            -- first positional and there is no receiver to split off.
                            if fn.isClassMethod then
                              applyFunc ctx n h₁ fn none (fn.ownerClassValue :: vs) kws
                            else if fn.isMethod && fn.vararg.isNone
                               && vs.length == fn.params.length + 1 then
                              applyFunc ctx n h₁ fn (some (vs.headD .unit)) vs.tail kws
                            else applyFunc ctx n h₁ fn none vs kws
                          | none    => (h₁, .hole s!"call:{g}")
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
            -- `len(x)`, `bool(x)`, `hash(x)`, `str(x)`, `repr(x)` on an ordinary instance
            -- whose class defines the dunder run the method (`builtinDunderTarget`); the
            -- answer is type-checked as CPython does (`builtinDunderResult`).
            match builtinDunderTarget ctx h₁ f vs with
            | some (r, cls, m) =>
              if kws.isEmpty then
                match ctx.resolveMethod cls m with
                | some fn =>
                  match applyFunc ctx n h₁ fn (some (.ref r)) [] [] with
                  | (h₂, .val v) => (h₂, builtinDunderResult f m v)
                  | (h₂, e)      => (h₂, e)
                | none => (h₁, .hole s!"call:{f}:dunder-unresolved")
              else (h₁, .hole s!"call:{f}:keyword-to-builtin")
            | none =>
            -- Modelled stdlib is consulted LAST, so a user function of the same name
            -- always wins. `builtin` returns `none` for anything it cannot model
            -- faithfully, which falls through to a visible hole.
            -- `Stdlib.builtin` takes positional arguments only: a keyword argument to a
            -- builtin is *not* passed silently, it is a named hole.
            if kws.isEmpty then
              match Stdlib.builtin ctx.dialect h₁ f vs with
              | some (h₂, r) => (h₂, r)
              | none         => (h₁, .hole s!"call:{f}")
            else (h₁, .hole s!"call:{f}:keyword-to-builtin")
  | n+1, h, ρ, .callValue fe args =>
      -- `f(x)(y)`, `d["k"](3)`: the callee is a VALUE. Evaluate it first (CPython's order),
      -- then the arguments, then dispatch exactly as `call` does for a name bound to a
      -- function value: a `.fn` resolves and applies (with the unbound-method and
      -- `@classmethod` rules), a `.clos` applies with its captures, a boxed function object
      -- calls what it carries. Anything else is not callable and says so. There is no
      -- builtin fallback: a builtin reached as a value has no name to look up.
      match evalExpr ctx n h ρ fe with
      | (h₁, .val fv) =>
        match evalList ctx n h₁ ρ args with
        | (h₂, .inl r)  => (h₂, r)
        | (h₂, .inr (vs, kws)) =>
          match fv with
          | .fn g      => match ctx.resolve g with
                          | some fn =>
                            if fn.isClassMethod then
                              applyFunc ctx n h₂ fn none (fn.ownerClassValue :: vs) kws
                            else if fn.isMethod && fn.vararg.isNone
                               && vs.length == fn.params.length + 1 then
                              applyFunc ctx n h₂ fn (some (vs.headD .unit)) vs.tail kws
                            else applyFunc ctx n h₂ fn none vs kws
                          | none    => (h₂, .hole s!"call:{g}")
          | .clos g cap => match ctx.resolve g with
                          | some fn => applyClosure ctx n h₂ fn cap vs kws
                          | none    => (h₂, .hole s!"call:{g}")
          | .ref addr  =>
            match unboxFn h₂ addr with
            | some (.fn g)      => match ctx.resolve g with
                                   | some fn => applyFunc ctx n h₂ fn none vs kws
                                   | none    => (h₂, .hole s!"call:{g}")
            | some (.clos g cap) => match ctx.resolve g with
                                    | some fn => applyClosure ctx n h₂ fn cap vs kws
                                    | none    => (h₂, .hole s!"call:{g}")
            | _ => (h₂, .hole "call:value:not-callable")
          | _ => (h₂, .hole "call:value:not-callable")
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .mcall recv m args =>
      match evalExpr ctx n h ρ recv with
      | (h₁, .val (.ref r)) =>
        match evalList ctx n h₁ ρ args with
        | (h₂, .inl e)  => (h₂, e)
        | (h₂, .inr (vs, kws)) =>
          match h₂.get r with
          | none   => (h₂, .hole "mcall:dangling-ref")
          | some o =>
            match ctx.resolveMethod o.cls m with
            | none    =>
              -- Boxed containers, step 3 (`docs/boxed-containers.md` §2). The user class
              -- has already been consulted and lost, so a container payload gets the
              -- builtin behaviour -- on the payload, writing any mutation back through
              -- `setPayload` so aliases observe it. Inert until something constructs a
              -- payload; `Payload.toVal` is `none` for every object Core builds today.
              match o.payload.toVal with
              | some pay =>
                  if kws.isEmpty then
                    match Stdlib.method ctx.dialect h₂ pay m vs with
                    | some (h₃, .pure res) => (h₃, res)
                    | some (h₃, .mutating res nv) =>
                        match Payload.ofVal nv with
                        | some np => (h₃.setPayload r np, res)
                        -- A mutating builtin whose new receiver is not a container.
                        -- Writing it back would change what the object IS.
                        | Option.none => (h₃, .hole s!"mcall:{m}:payload-kind-changed")
                    | Option.none => (h₂, .hole s!"mcall:{o.cls}.{m}")
                  -- Same refusal the unboxed path makes: `Stdlib.method` has no keyword
                  -- calling convention, and dropping keywords silently is the bug the
                  -- varargs work fixed.
                  else (h₂, .hole s!"mcall:{m}:keyword-to-builtin")
              | Option.none =>
              -- `keys.hashkey(x)` on a **module object**. A module has no methods, so
              -- `resolveMethod` finds nothing; what it has is a *field* holding a
              -- function value, and a module-level function takes no receiver. Calling
              -- it with `self` bound would shift every argument by one, so the receiver
              -- is dropped — which is exactly what CPython does for an attribute that is
              -- a plain function rather than a class attribute.
              --
              -- The same rule holds for an ORDINARY instance whose attribute holds a
              -- function or closure: `self.cb(x)` does not pass `self` in CPython
              -- either. It was kept module-only "until measured on its own"; the
              -- differential oracle measured it on click 8.2.1 (`FuncParamType.convert`,
              -- `self.func(value)`: three divergences, docs/languages.md §10.9), so the
              -- lookup now runs for every object and only the hole LABELS still tell a
              -- module object from an instance.
              match o.fields.find? (·.1 == m) with
              | some (_, .fn g)      =>
                  match ctx.resolve g with
                  | some fn => applyFunc ctx n h₂ fn none vs kws
                  | none    => (h₂, .hole s!"call:{g}")
              | some (_, .clos g cap) =>
                  match ctx.resolve g with
                  | some fn => applyClosure ctx n h₂ fn cap vs kws
                  | none    => (h₂, .hole s!"call:{g}")
              | some _  =>
                  if o.cls.startsWith "<module>" then (h₂, .hole s!"module-call:{m}:not-a-function")
                  else (h₂, .hole s!"mcall:{o.cls}.{m}:field-not-callable")
              | none    =>
                  if o.cls.startsWith "<module>" then (h₂, .hole s!"module-attr:{m}")
                  else (h₂, .hole s!"mcall:{o.cls}.{m}")
            | some fn =>
              -- `c.make(3)` on a `@classmethod`: Python passes the CLASS, not `c`, and
              -- passes it as the first positional (the exporter kept `cls` in `params`),
              -- so there is no receiver to inject under `self`.
              if fn.isClassMethod then
                applyFunc ctx n h₂ fn none (fn.ownerClassValue :: vs) kws
              else if o.captured.isEmpty then applyFunc ctx n h₂ fn (some (.ref r)) vs kws
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
          if ctx.classDefines short m then
            match ctx.resolveMethod short m with
            | some fn =>
                -- `C.make(3)` on a `@classmethod`: the receiver IS this class value, and
                -- it goes in as the first positional rather than as `self`. An unbound
                -- ordinary method keeps the split-off rule below.
                if fn.isClassMethod then
                  applyFunc ctx n h₂ fn none ((.fn g) :: vs) kws
                else match vs with
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
        | (h₂, .inr (_, _ :: _)) => (h₂, .hole s!"mcall:{m}:keyword-to-builtin")
        | (h₂, .inr (vs, [])) =>
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
          let fields := (List.range len.toNat).map (fun i => (toString i, Val.unit))
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
      | (h₁, .val (.iref r sel)) => (h₁, .val (h₁.getField r sel.key))
      | (h₁, .val _)             => (h₁, .hole "derefIref:non-iref")
      | (h₁, res)                => (h₁, res)
  | n+1, h, ρ, .alloc cls args =>
      match evalList ctx n h ρ args with
      | (h₁, .inl r)  => (h₁, r)
      | (h₁, .inr (vs, kws)) =>
        match ctx.builtinBase cls with
        -- `class X(tuple)` and friends: the instance IS the builtin, not an opaque
        -- reference. See `Val.bobj`.
        | some b => (h₁, allocBuiltin ctx cls b vs)
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
      if kwargsRejected fn kws || posRejected fn vs || signatureRejected fn vs kws then
        (h, .exn (.str "TypeError")) else
      -- Class-attribute defaults are resolved HERE, not in `bindParams`: they need the
      -- heap, and `bindParams` is heap-free by design (re-typing it is the `applyBinop`
      -- problem). Arity was already checked above, so a hole from this step is about a
      -- class attribute, never about the call shape. For a function with no such
      -- defaults this is `.inr (selfEnv self?)` by unfolding and nothing changes.
      match seedClassAttrDefaults ctx h fn (selfEnv self?) vs kws with
      | .inl l     => (h, .hole l)
      | .inr base' =>
      let ρ := bindParams fn base' vs kws
      match execStmt ctx n h ρ fn.body with
      | (h₁, .ret v _)  => (h₁, .val v)
      | (h₁, .normal _) => (h₁, .val .unit)
      | (h₁, .exn v _)  => (h₁, .exn v)
      | (h₁, .hole l)   => (h₁, .hole l)
      | (h₁, .outOfFuel)=> (h₁, .outOfFuel)
      | (h₁, _)         => (h₁, .hole "call:stray-control-flow")

/-- Apply a closure: the captured bindings form the base environment, then parameters
shadow them.

Capture is by value. Reads of enclosing variables therefore work, which covers decorators
and factory functions; a `nonlocal` **write** would need the binding to be a shared
mutable cell, so the transpiler keeps it as an explicit hole rather than pretending. -/
def applyClosure (ctx : Ctx) : Nat → Heap → Func → List (String × Val) → List Val →
    List (String × Val) → Heap × EResult
  | 0,   h, _,  _,   _,  _   => (h, .outOfFuel)
  | n+1, h, fn, cap, vs, kws =>
      if kwargsRejected fn kws || posRejected fn vs || signatureRejected fn vs kws then
        (h, .exn (.str "TypeError")) else
      -- Same class-attribute seeding as `applyFunc`; the captured bindings are the base.
      match seedClassAttrDefaults ctx h fn cap vs kws with
      | .inl l     => (h, .hole l)
      | .inr base' =>
      let ρ : Env := bindParams fn base' vs kws
      match execStmt ctx n h ρ fn.body with
      | (h₁, .ret v _)   => (h₁, .val v)
      | (h₁, .normal _)  => (h₁, .val .unit)
      | (h₁, .exn v _)   => (h₁, .exn v)
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
        match (v.unbox h₁).iterable with
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
        match strKeyed (v.unbox h₁) with
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
      | (h₁, .exn v)     => (h₁, .exn v ρ)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .setGlobal x e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v)     => (h₁.setField ctx.globals x v, .normal ρ)
      | (h₁, .exn v)     => (h₁, .exn v ρ)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .assign x e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v)     =>
          if (ρ.get ("<glob>" ++ x)).truthy then (h₁.setField ctx.globals x v, .normal ρ)
          else (h₁, .normal (ρ.set x v))
      | (h₁, .exn v)     => (h₁, .exn v ρ)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .ret e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v)     => (h₁, .ret v ρ)
      | (h₁, .exn v)     => (h₁, .exn v ρ)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .raise e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v)     =>
          -- Python classifies the raised value (`pythonRaise`). Every other dialect throws
          -- whatever it was given: Java and C++ throw arbitrary objects, and Core has no
          -- exception-object representation to check them against.
          if ctx.dialect == .python then
            match pythonRaise v with
            | .exn w     => (h₁, .exn w ρ)
            | .hole l    => (h₁, .hole l)
            | .val _     => (h₁, .hole "raise:non-exception-value")
            | .outOfFuel => (h₁, .outOfFuel)
          else (h₁, .exn v ρ)
      | (h₁, .exn v)     => (h₁, .exn v ρ)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .setField r f v =>
      match evalExpr ctx n h ρ r with
      | (h₁, .val (.ref addr)) =>
        match evalExpr ctx n h₁ ρ v with
        -- JavaScript: `o.k = v` on an object literal writes the KEY of its boxed dict
        -- (`jsContainerField` is the matching read); on anything else it is a field
        -- write exactly as in Python. `setPayload` bumps the version, as every payload
        -- write must.
        | (h₂, .val vv)    =>
            if ctx.dialect == .javascript then
              match h₂.payload addr with
              | .dict kvs => (h₂.setPayload addr (.dict (Stdlib.dictSet kvs (.str f) vv)), .normal ρ)
              | _         => (h₂.setField addr f vv, .normal ρ)
            else (h₂.setField addr f vv, .normal ρ)
        | (h₂, .exn e)     => (h₂, .exn e ρ)
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
            | (h₃, .exn e)     => (h₃, .exn e ρ)
            | (h₃, .hole l)    => (h₃, .hole l)
            | (h₃, .outOfFuel) => (h₃, .outOfFuel)
          else (h₁, .hole s!"setField:{f}:non-object")
        | _ => (h₁, .hole s!"setField:{f}:non-object")
      | (h₁, .exn e) => (h₁, .exn e ρ)
      | (h₁, .hole l) => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .setIndex e i v =>
      -- Boxed containers, step 3 (`docs/boxed-containers.md` §2). A container that lives
      -- in the heap as an `Obj` payload can be mutated; a `Val.list`/`Val.dict` *value*
      -- still cannot, and keeps the hole -- that case is ignorance, not a TypeError.
      -- Inert until something constructs a payload, which is deliberate: the same staging
      -- step 1 used, so the semantics can be written and tested before the switchover
      -- moves any number.
      --
      -- Order is v, then e, then i -- CPython evaluates the RHS FIRST. Confirmed by
      -- execution, and it is not what §2's pseudocode shows.
      match evalExpr ctx n h ρ v with
      | (h₁, .val vv) =>
        match evalExpr ctx n h₁ ρ e with
        | (h₂, .val (.ref r)) =>
          match evalExpr ctx n h₂ ρ i with
          | (h₃, .val iv) =>
            match h₃.payload r with
            | .list vs =>
                match iv with
                | .int k =>
                    match Stdlib.seqIndex vs.length k with
                    | some j => (h₃.setPayload r (.list (vs.set j vv)), .normal ρ)
                    | none   => (h₃, .exn (.str "IndexError") ρ)
                | _ => (h₃, .exn (.str "TypeError") ρ)
            | .dict kvs => (h₃.setPayload r (.dict (Stdlib.dictSet kvs iv vv)), .normal ρ)
            -- A `tuple` SUBCLASS instance: immutable, and Python says so with a value.
            | .tuple _  => (h₃, .exn (.str "TypeError") ρ)
            -- An ordinary instance: `c[k] = v` IS `c.__setitem__(k, v)` when the class
            -- defines it. A class that does not stays ignorance rather than becoming a
            -- TypeError that would be wrong for a class that inherits one.
            | .none     =>
                match ctx.dunderOn h₃ (.ref r) "__setitem__" with
                | some (_, fn) =>
                    match applyFunc ctx n h₃ fn (some (.ref r)) [iv, vv] [] with
                    | (h₄, .val _)     => (h₄, .normal ρ)
                    | (h₄, .exn e)     => (h₄, .exn e ρ)
                    | (h₄, .hole l)    => (h₄, .hole l)
                    | (h₄, .outOfFuel) => (h₄, .outOfFuel)
                | none => (h₃, .hole "setIndex:immutable-containers")
          | (h₃, .exn ex)   => (h₃, .exn ex ρ)
          | (h₃, .hole l)   => (h₃, .hole l)
          | (h₃, .outOfFuel) => (h₃, .outOfFuel)
        | (h₂, .val _)    => (h₂, .hole "setIndex:immutable-containers")
        | (h₂, .exn ex)   => (h₂, .exn ex ρ)
        | (h₂, .hole l)   => (h₂, .hole l)
        | (h₂, .outOfFuel) => (h₂, .outOfFuel)
      | (h₁, .exn ex)   => (h₁, .exn ex ρ)
      | (h₁, .hole l)   => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .delIndex e i =>
      -- `del e[i]` (`docs/boxed-containers.md` §2), mirroring `setIndex`. Order is e then
      -- i -- there is no RHS here, and CPython evaluates target before index.
      match evalExpr ctx n h ρ e with
      | (h₁, .val (.ref r)) =>
        match evalExpr ctx n h₁ ρ i with
        | (h₂, .val iv) =>
          match h₂.payload r with
          | .list vs =>
              match iv with
              | .int k =>
                  match Stdlib.seqIndex vs.length k with
                  | some j => (h₂.setPayload r (.list (Stdlib.dropAt vs j)), .normal ρ)
                  | none   => (h₂, .exn (.str "IndexError") ρ)
              | _ => (h₂, .exn (.str "TypeError") ρ)
          | .dict kvs =>
              if Stdlib.dictHas kvs iv then
                (h₂.setPayload r (.dict (Stdlib.dictDel kvs iv)), .normal ρ)
              else (h₂, .exn (.str "KeyError") ρ)
          | .tuple _ => (h₂, .exn (.str "TypeError") ρ)
          -- An ordinary instance: `del c[k]` IS `c.__delitem__(k)` when the class defines it.
          | .none    =>
              match ctx.dunderOn h₂ (.ref r) "__delitem__" with
              | some (_, fn) =>
                  match applyFunc ctx n h₂ fn (some (.ref r)) [iv] [] with
                  | (h₃, .val _)     => (h₃, .normal ρ)
                  | (h₃, .exn e)     => (h₃, .exn e ρ)
                  | (h₃, .hole l)    => (h₃, .hole l)
                  | (h₃, .outOfFuel) => (h₃, .outOfFuel)
              | none => (h₂, .hole "delIndex:immutable-containers")
        | (h₂, .exn ex)    => (h₂, .exn ex ρ)
        | (h₂, .hole l)    => (h₂, .hole l)
        | (h₂, .outOfFuel) => (h₂, .outOfFuel)
      | (h₁, .val _)     => (h₁, .hole "delIndex:immutable-containers")
      | (h₁, .exn ex)    => (h₁, .exn ex ρ)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .setSlice e lo hi st v =>
      -- `xs[lo:hi:st] = v`. Order is v, then e, then lo, hi, st: CPython evaluates the
      -- RHS first, exactly as for `setIndex`. The RHS is any iterable -- a boxed list is
      -- looked through, a string contributes its characters -- and a non-iterable is a
      -- `TypeError`. A unit step replaces the range whatever the RHS length; an extended
      -- step requires equal lengths and is otherwise a `ValueError`. Both from CPython.
      match evalExpr ctx n h ρ v with
      | (h₁, .val vv) =>
        match evalExpr ctx n h₁ ρ e with
        | (h₂, .val (.ref r)) =>
          match evalExpr ctx n h₂ ρ lo with
          | (h₃, .val lv) =>
            match evalExpr ctx n h₃ ρ hi with
            | (h₄, .val hv) =>
              match evalExpr ctx n h₄ ρ st with
              | (h₅, .val sv) =>
                match h₅.payload r with
                | .list vs =>
                    match Stdlib.sliceBound lv, Stdlib.sliceBound hv, Stdlib.sliceBound sv with
                    | some lo', some hi', some st' =>
                        match (vv.unbox h₅).iterable with
                        | none    => (h₅, .exn (.str "TypeError") ρ)
                        | some ys =>
                            match Stdlib.listSetSlice vs lo' hi' st' ys with
                            | .ok vs'    => (h₅.setPayload r (.list vs'), .normal ρ)
                            | .error ex  => (h₅, .exn (.str ex) ρ)
                    | _, _, _ => (h₅, .exn (.str "TypeError") ρ)
                -- A `tuple` subclass instance is immutable; a dict cannot take a slice
                -- key ("unhashable type: 'slice'"). Both are Python `TypeError`s.
                | .tuple _ => (h₅, .exn (.str "TypeError") ρ)
                | .dict _  => (h₅, .exn (.str "TypeError") ρ)
                | .none    => (h₅, .hole "setSlice:immutable-containers")
              | (h₅, .exn ex)    => (h₅, .exn ex ρ)
              | (h₅, .hole l)    => (h₅, .hole l)
              | (h₅, .outOfFuel) => (h₅, .outOfFuel)
            | (h₄, .exn ex)    => (h₄, .exn ex ρ)
            | (h₄, .hole l)    => (h₄, .hole l)
            | (h₄, .outOfFuel) => (h₄, .outOfFuel)
          | (h₃, .exn ex)    => (h₃, .exn ex ρ)
          | (h₃, .hole l)    => (h₃, .hole l)
          | (h₃, .outOfFuel) => (h₃, .outOfFuel)
        | (h₂, .val _)     => (h₂, .hole "setSlice:immutable-containers")
        | (h₂, .exn ex)    => (h₂, .exn ex ρ)
        | (h₂, .hole l)    => (h₂, .hole l)
        | (h₂, .outOfFuel) => (h₂, .outOfFuel)
      | (h₁, .exn ex)    => (h₁, .exn ex ρ)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .delSlice e lo hi st =>
      -- `del xs[lo:hi:st]`: receiver, then bounds. Removes exactly the positions the
      -- slice denotes, so `del xs[::2]` works too.
      match evalExpr ctx n h ρ e with
      | (h₁, .val (.ref r)) =>
        match evalExpr ctx n h₁ ρ lo with
        | (h₂, .val lv) =>
          match evalExpr ctx n h₂ ρ hi with
          | (h₃, .val hv) =>
            match evalExpr ctx n h₃ ρ st with
            | (h₄, .val sv) =>
              match h₄.payload r with
              | .list vs =>
                  match Stdlib.sliceBound lv, Stdlib.sliceBound hv, Stdlib.sliceBound sv with
                  | some lo', some hi', some st' =>
                      match Stdlib.sliceIndices vs.length lo' hi' st' with
                      | none    => (h₄, .exn (.str "ValueError") ρ)
                      | some ks => (h₄.setPayload r (.list (Stdlib.listDelIdx vs ks)), .normal ρ)
                  | _, _, _ => (h₄, .exn (.str "TypeError") ρ)
              | .tuple _ => (h₄, .exn (.str "TypeError") ρ)
              | .dict _  => (h₄, .exn (.str "TypeError") ρ)
              | .none    => (h₄, .hole "delSlice:immutable-containers")
            | (h₄, .exn ex)    => (h₄, .exn ex ρ)
            | (h₄, .hole l)    => (h₄, .hole l)
            | (h₄, .outOfFuel) => (h₄, .outOfFuel)
          | (h₃, .exn ex)    => (h₃, .exn ex ρ)
          | (h₃, .hole l)    => (h₃, .hole l)
          | (h₃, .outOfFuel) => (h₃, .outOfFuel)
        | (h₂, .exn ex)    => (h₂, .exn ex ρ)
        | (h₂, .hole l)    => (h₂, .hole l)
        | (h₂, .outOfFuel) => (h₂, .outOfFuel)
      | (h₁, .val _)     => (h₁, .hole "delSlice:immutable-containers")
      | (h₁, .exn ex)    => (h₁, .exn ex ρ)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  -- `006-reduce-remaining-holes`, Story 5: `*p = v`, `p` an interior-pointer VALUE --
  -- requires the pointer operand to evaluate to `Val.iref r sel` and delegates,
  -- unconditionally, to the unchanged `Heap.setField`.
  | n+1, h, ρ, .setDerefIref p v =>
      match evalExpr ctx n h ρ p with
      | (h₁, .val (.iref r sel)) =>
        match evalExpr ctx n h₁ ρ v with
        | (h₂, .val vv)    => (h₂.setField r sel.key vv, .normal ρ)
        | (h₂, .exn e)     => (h₂, .exn e ρ)
        | (h₂, .hole l)    => (h₂, .hole l)
        | (h₂, .outOfFuel) => (h₂, .outOfFuel)
      | (h₁, .val _)      => (h₁, .hole "setDerefIref:non-iref")
      | (h₁, .exn e)      => (h₁, .exn e ρ)
      | (h₁, .hole l)     => (h₁, .hole l)
      | (h₁, .outOfFuel)  => (h₁, .outOfFuel)
  | n+1, h, ρ, .seq a b =>
      match execStmt ctx n h ρ a with
      | (h₁, .normal ρ') => execStmt ctx n h₁ ρ' b
      | (h₁, r)          => (h₁, r)
  | n+1, h, ρ, .ifte c t e =>
      match evalExpr ctx n h ρ c with
      | (h₁, .val v)     => if v.truthy then execStmt ctx n h₁ ρ t
                            else execStmt ctx n h₁ ρ e
      | (h₁, .exn v)     => (h₁, .exn v ρ)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .tryFinally body fin =>
      match execStmt ctx n h ρ body with
      -- These are interpreter failures, not language exits. Running a finalizer
      -- on a partial execution could turn unsupported or unfinished work into a proof.
      | (h₁, .hole l) => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
      | (h₁, .normal ρ') => execStmt ctx n h₁ ρ' fin
      | (h₁, r) =>
          -- The finalizer runs on every language exit. An abnormal exit discards the
          -- body's pending outcome: `try: return 1 finally: return 2` returns 2.
          match execStmt ctx n h₁ (r.env ρ) fin with
          | (h₂, .normal ρ') => (h₂, r.withEnv ρ')
          | (h₂, r')        => (h₂, r')
  | n+1, h, ρ, .tryCatch body x handler =>
      match execStmt ctx n h ρ body with
      | (h₁, .exn v ρ') => execStmt ctx n h₁ (ρ'.set x v) handler
      | (h₁, r)      => (h₁, r)
  | n+1, h, ρ, .loop c body =>
      match evalExpr ctx n h ρ c with
      | (h₁, .val v) =>
          if v.truthy then
            match execStmt ctx n h₁ ρ body with
            | (h₂, .normal ρ') => execStmt ctx n h₂ ρ' (.loop c body)
            | (h₂, .cont ρ')   => execStmt ctx n h₂ ρ' (.loop c body)
            | (h₂, .brk ρ')    => (h₂, .normal ρ')
            | (h₂, r)          => (h₂, r)
          else (h₁, .normal ρ)
      | (h₁, .exn v)     => (h₁, .exn v ρ)
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
        -- A boxed container iterates LIVE; everything else keeps the snapshot, which is
        -- exactly right for a `Val.tuple` or `Val.str` and is all Core can do for an
        -- unboxed `Val.list` anyway.
        match v with
        | .ref r =>
            match h₁.payload r with
            | .none => match v.iterable with
                       | some vs => execFor ctx n h₁ ρ x vs body
                       | none    => (h₁, .hole "forIn:non-iterable")
            | _     => execForRef ctx n h₁ ρ x r 0 ((h₁.get r).elim 0 (·.version)) body
        | _ =>
            match v.iterable with
            | some vs => execFor ctx n h₁ ρ x vs body
            | none    => (h₁, .hole "forIn:non-iterable")
      | (h₁, .exn v)     => (h₁, .exn v ρ)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)

/-- Live iteration over a **boxed** container (`docs/boxed-containers.md` §4).

Snapshot iteration is wrong the moment a container can be mutated mid-loop, and §4 is
explicit that it must not survive boxing: landing boxing beside a snapshot loop would
introduce a silent wrong answer in the same change that removes one. So this re-reads the
payload at every step instead of copying it once.

The two containers differ, and CPython is the authority for both:

* a `list` iterator holds the object and an index, so appending during the loop extends
  it and deleting shortens it -- no error, just a different number of iterations;
* a `dict` iterator raises `RuntimeError: dictionary changed size during iteration`.
  `Obj.version` exists for this: the version is recorded when the loop starts and checked
  at every step, which turns an invisible wrong answer into a modelled exception.

A `tuple` payload is immutable, so re-reading it is the same as a snapshot. -/
def execForRef (ctx : Ctx) :
    Nat → Heap → Env → String → Ref → Nat → Nat → Stmt → Heap × Ctl
  | 0,   h, _, _, _, _, _, _ => (h, .outOfFuel)
  | n+1, h, ρ, x, r, i, ver, body =>
      match h.payload r with
      | .list vs =>
          match vs[i]? with
          | none   => (h, .normal ρ)
          | some v =>
            match execStmt ctx n h (ρ.set x v) body with
            | (h₁, .normal ρ') => execForRef ctx n h₁ ρ' x r (i+1) ver body
            | (h₁, .cont ρ')   => execForRef ctx n h₁ ρ' x r (i+1) ver body
            | (h₁, .brk ρ')    => (h₁, .normal ρ')
            | (h₁, res)        => (h₁, res)
      | .tuple vs =>
          match vs[i]? with
          | none   => (h, .normal ρ)
          | some v =>
            match execStmt ctx n h (ρ.set x v) body with
            | (h₁, .normal ρ') => execForRef ctx n h₁ ρ' x r (i+1) ver body
            | (h₁, .cont ρ')   => execForRef ctx n h₁ ρ' x r (i+1) ver body
            | (h₁, .brk ρ')    => (h₁, .normal ρ')
            | (h₁, res)        => (h₁, res)
      | .dict kvs =>
          if ((h.get r).elim 0 (·.version)) != ver then
            (h, .exn (.str "RuntimeError") ρ)
          else
            match kvs[i]? with
            | none        => (h, .normal ρ)
            | some (k, _) =>
              match execStmt ctx n h (ρ.set x k) body with
              | (h₁, .normal ρ') => execForRef ctx n h₁ ρ' x r (i+1) ver body
              | (h₁, .cont ρ')   => execForRef ctx n h₁ ρ' x r (i+1) ver body
              | (h₁, .brk ρ')    => (h₁, .normal ρ')
              | (h₁, res)        => (h₁, res)
      | .none => (h, .hole "forIn:non-iterable")

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
                     builtinBases := p.builtinBases, properties := p.properties }
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
                     builtinBases := p.builtinBases, properties := p.properties }
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
                     builtinBases := p.builtinBases, properties := p.properties }
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
-- Python, so under `.python` the same term is the hole it has always been. The label
-- sharpened when dicts became objects: the receiver IS an object now, just one whose
-- payload is a container and which therefore has no `__dict__` to miss into.
/-- info: Autoform.Core.EResult.hole "field:cra_priority:on-container" -/
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

/-! ## Module-level variables are module attributes

Language Reference §3.2.9 (Modules): a module's namespace is a dictionary and `m.x` is
`m.__dict__["x"]`; §5.4.1 (Loaders): the module body executes in that dictionary; §7.11
(The `import` statement): `from m import x` stores "a reference to that value" in the
importing namespace. So the exporter lowers a module-level binding `X = e` to the
globals-frame write it always was PLUS a write of the module object's field `X`, and
`from a import X` to a read of that field at import time -- the value `a`'s body bound,
copied once, as CPython binds it. `a.X` stays a `.field` read at use time.

    # a.py
    LIMIT = 3
    # b.py
    from a import LIMIT
    from a import LIMIT as L
    import a
    def f(): return LIMIT + 1
    def viaAttr(): return a.LIMIT
    def alias(): return L
    def missing(): return a.NOPE

CPython: `f()` is `4`, `viaAttr()` is `3`, `alias()` is `3`, `missing()` raises
`AttributeError`. Core answers the first three exactly and refuses the fourth with the
module object's named miss. The initializers run in import-dependency order (`a` before
`b`, as §5.4 loads `a` when `b` first imports it); the last check shows what a WRONG
order gives -- a named hole, never a value. -/
def modVarProg : Program :=
  { dialect := .python
  , funcs :=
    [ { name := "b.py:<module>.f", params := []
      , body := .ret (.binop "+" (.name "LIMIT") (.lit (.int 1))) }
    , { name := "b.py:<module>.viaAttr", params := []
      , body := .ret (.field (.name "<module>a.py") "LIMIT") }
    , { name := "b.py:<module>.alias", params := []
      , body := .ret (.name "L") }
    , { name := "b.py:<module>.missing", params := []
      , body := .ret (.field (.name "<module>a.py") "NOPE") } ] }

/-- `<module-objects>`: one object per module, allocated before any body runs. -/
def modVarObjects : Func :=
  { name := "<module-objects>:<module>", params := []
  , body :=
      .seq (.setGlobal "<module>a.py" (.alloc "<module>a.py" []))
           (.setGlobal "<module>b.py" (.alloc "<module>b.py" [])) }

/-- `a.py`'s body: `LIMIT = 3`, lowered by `bindName` -- the globals-frame write and the
module object's field, in that order, so the field holds what the body computed. -/
def modVarAInit : Func :=
  { name := "a.py:<module>", params := []
  , body :=
      .seq (.setGlobal "LIMIT" (.lit (.int 3)))
           (.setField (.name "<module>a.py") "LIMIT" (.name "LIMIT")) }

/-- `b.py`'s body: the two `from a import` forms, each a field read at import time. -/
def modVarBInit : Func :=
  { name := "b.py:<module>", params := []
  , body :=
      .seq (.setGlobal "LIMIT" (.field (.name "<module>a.py") "LIMIT"))
           (.setGlobal "L" (.field (.name "<module>a.py") "LIMIT")) }

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 4) -/
#guard_msgs in #eval runMain modVarProg 200 [modVarObjects, modVarAInit, modVarBInit] "b.py:<module>.f" []

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 3) -/
#guard_msgs in #eval runMain modVarProg 200 [modVarObjects, modVarAInit, modVarBInit] "b.py:<module>.viaAttr" []

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 3) -/
#guard_msgs in #eval runMain modVarProg 200 [modVarObjects, modVarAInit, modVarBInit] "b.py:<module>.alias" []

/-! `a.NOPE`: never bound, so the module object names the miss (CPython: `AttributeError`). -/
/-- info: Autoform.Core.EResult.hole "module-attr:NOPE" -/
#guard_msgs in #eval runMain modVarProg 200 [modVarObjects, modVarAInit, modVarBInit] "b.py:<module>.missing" []

/-! The order matters, and getting it wrong is loud: with `b`'s body before `a`'s, the
import-time read finds no field yet and the initializer stops at the named hole, exactly
where CPython's `from a import LIMIT` would have been the statement that runs `a` first. -/
/-- info: Autoform.Core.EResult.hole "module-attr:LIMIT" -/
#guard_msgs in #eval runMain modVarProg 200 [modVarObjects, modVarBInit, modVarAInit] "b.py:<module>.f" []

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

/-- `Lit.toVal` is exactly what `evalExpr` produces for a literal.

`Syntax.lean` claims this where `Lit.toVal` is defined, and the claim is load-bearing:
`bindParams` uses `Lit.toVal` to bind a literal default without going through `evalExpr`,
so if the two ever disagreed, a default would bind a different value than the same
literal written out at the call site. That is a silent wrong answer, not a hole, which is
the failure class this project spends its oracles on. Stated here rather than left to
inspection so that a new `Lit` constructor cannot be added to one and not the other. -/
@[simp] theorem Lit.toVal_agrees_with_evalExpr
    (ctx : Ctx) (n : Nat) (h : Heap) (ρ : Env) (l : Lit) :
    evalExpr ctx (n + 1) h ρ (.lit l) = (h, .val l.toVal) := by
  cases l <;> rfl

/-! ## A closure cell, from primitives Core already has

`cartographer/export_ast.sc` holes every `nonlocal` write as `scope:nonlocal-write`, and
its comment gives the reason: `Expr.closure` captures the environment **by value**, so a
write can never be observed by the frame that owns the variable, and emitting an `assign`
would produce a program that runs and quietly computes the wrong answer.

That reason is correct about `assign` and wrong about Core. Capturing a `Val.ref` by value
still shares the object it points at, which is exactly how a compiler implements a closure
cell: `boxNew` allocates it, `field`/`setField` read and write through it. The program
below is the `hits += 1` shape from `cachetools/_cached.py` -- two calls through a closure,
and the owning frame sees both writes.

So `scope:nonlocal-write` is **not** blocked on the trusted semantics. It is blocked on the
exporter, which translates one method at a time, while converting a variable to a cell is a
whole-scope rewrite: box it where it is defined, then rewrite every read and write of it in
that scope and in every nested one. Missing a single read site yields a stale value with no
hole marking it -- which is why this is still a hole and not a translation. -/
private def cellProg : Program :=
  { dialect := .python
  , funcs :=
    [ { name := "bump", params := []
      , body := .setField (.name "cell") "v"
                  (.binop "+" (.field (.name "cell") "v") (.lit (.int 1))) }
    , { name := "outer", params := []
      , body :=
          .seq (.assign "cell" (.boxNew (.lit (.int 0))))
          (.seq (.assign "f" (.closure "bump"))
          (.seq (.expr (.call "f" []))
          (.seq (.expr (.call "f" []))
                (.ret (.field (.name "cell") "v"))))) } ] }

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 2) -/
#guard_msgs in #eval runFunc cellProg 200 "outer" []

/-! ## Value-callees: `f(x)(y)`, `d["k"](3)`, and a non-callable

`Expr.callValue` applies whatever its callee EVALUATES to. Every expectation is CPython's:
`mk(10)(2)` runs the closure `mk` returned; a function fetched out of a dict is called
with the dict's element as callee; calling `5` is a `TypeError` in CPython and a named
hole here, because Core does not raise on its own behalf for a shape it cannot dispatch. -/
private def valueCallProg : Program :=
  { dialect := .python
  , funcs :=
    [ { name := "inner", params := ["y"]
      , body := .ret (.binop "+" (.name "y") (.name "k")) }
    , { name := "mk", params := ["k"]
      , body := .ret (.closure "inner") }
    , { name := "twice", params := ["x"]
      , body := .ret (.binop "*" (.name "x") (.lit (.int 2))) }
    -- `mk(10)(2)`: the callee is itself a call.
    , { name := "chained", params := []
      , body := .ret (.callValue (.call "mk" [.lit (.int 10)]) [.lit (.int 2)]) }
    -- `d = {"k": twice}; d["k"](3)`: the callee is an index into a dict of functions.
    , { name := "fromDict", params := []
      , body :=
          .seq (.assign "d" (.dictE [(.lit (.str "k"), .fnref "twice")]))
               (.ret (.callValue (.index (.name "d") (.lit (.str "k"))) [.lit (.int 3)])) }
    -- `5(1)`: not callable.
    , { name := "notCallable", params := []
      , body := .ret (.callValue (.lit (.int 5)) [.lit (.int 1)]) }
    -- `o = Box(); o.cb = twice; o.cb(21)`: a callable held in an INSTANCE FIELD is called
    -- through the attribute with no receiver, as CPython does (click's
    -- `FuncParamType.convert`, docs/languages.md §10.9).
    , { name := "fieldCall", params := []
      , body :=
          .seq (.assign "o" (.alloc "Box" []))
          (.seq (.setField (.name "o") "cb" (.fnref "twice"))
                (.ret (.mcall (.name "o") "cb" [.lit (.int 21)]))) } ] }

-- mk(10)(2)  -- CPython 12
#guard match runFunc valueCallProg 200 "chained" [] with | .val (.int 12) => true | _ => false
-- d["k"](3)  -- CPython 6
#guard match runFunc valueCallProg 200 "fromDict" [] with | .val (.int 6) => true | _ => false
-- 5(1)       -- CPython TypeError; Core: a named hole, never a value
#guard match runFunc valueCallProg 200 "notCallable" [] with
       | .hole "call:value:not-callable" => true | _ => false
-- o.cb = twice; o.cb(21)  -- CPython 42: the field's function, no receiver passed
#guard match runFunc valueCallProg 200 "fieldCall" [] with | .val (.int 42) => true | _ => false

/-! ## Boxed containers, step 3: `setIndex` on a heap payload

`docs/boxed-containers.md` §2. Nothing constructs a payload yet, so these are the only
programs that exercise the path — which is why it is landed this way: the semantics can be
written and checked before the switchover moves any measured number, exactly as step 1 was
landed inert.

Every expectation below was taken from CPython, not from the design document — whose
pseudocode also has the evaluation order wrong. It shows the target evaluated first;
CPython evaluates the RHS first, and `execStmt` follows CPython. -/
private def setIdxCtx : Ctx := { dialect := .python, table := [] }
/-- The same probes under a non-Python dialect, where a container literal is a VALUE and
must stay one: a C aggregate has no identity to share. -/
private def setIdxCtxC : Ctx := { dialect := .cLike, table := [] }
private def setIdxEnv : Env :=
  [("xs", .ref 0), ("d", .ref 1), ("t", .ref 2), ("o", .ref 3)]
private def setIdxHeap : Heap :=
  [ { cls := "list",  fields := [], payload := .list [.int 1, .int 2] }
  , { cls := "dict",  fields := [], payload := .dict [(.str "a", .int 1)] }
  , { cls := "T",     fields := [], payload := .tuple [.int 7] }
  , { cls := "Plain", fields := [] } ]
private def setIdx (tgt idx val : Expr) : Heap × Ctl :=
  execStmt setIdxCtx 50 setIdxHeap setIdxEnv (.setIndex tgt idx val)

-- `xs[0] = 9` on a list payload.  CPython: [9, 2]
#guard match (setIdx (.name "xs") (.lit (.int 0)) (.lit (.int 9))).1[0]!.payload with
       | .list [.int 9, .int 2] => true | _ => false

-- `d["b"] = 2`.  CPython: {'a': 1, 'b': 2} -- insertion order is observable.
#guard match (setIdx (.name "d") (.lit (.str "b")) (.lit (.int 2))).1[1]!.payload with
       | .dict [(.str "a", .int 1), (.str "b", .int 2)] => true | _ => false

-- Mutation bumps the version, so an iterator can tell that it happened.
#guard (setIdx (.name "xs") (.lit (.int 0)) (.lit (.int 9))).1[0]!.version == 1

-- Out of range is `IndexError` -- a value, not a hole.  CPython agrees.
#guard match (setIdx (.name "xs") (.lit (.int 5)) (.lit (.int 9))).2 with
       | .exn (.str "IndexError") _ => true | _ => false

-- A `tuple` subclass instance is immutable, and Python says so with a `TypeError`.
#guard match (setIdx (.name "t") (.lit (.int 0)) (.lit (.int 9))).2 with
       | .exn (.str "TypeError") _ => true | _ => false

-- An ordinary instance still holes. `__setitem__` dispatch is not part of this step, and
-- a `TypeError` here would be wrong for every class that defines one.
#guard match (setIdx (.name "o") (.lit (.int 0)) (.lit (.int 9))).2 with
       | .hole "setIndex:immutable-containers" => true | _ => false

private def delIdx (tgt idx : Expr) : Heap × Ctl :=
  execStmt setIdxCtx 50 setIdxHeap setIdxEnv (.delIndex tgt idx)

-- `del xs[0]`.  CPython: [2]
#guard match (delIdx (.name "xs") (.lit (.int 0))).1[0]!.payload with
       | .list [.int 2] => true | _ => false

-- `del d["a"]`.  CPython: {}
#guard match (delIdx (.name "d") (.lit (.str "a"))).1[1]!.payload with
       | .dict [] => true | _ => false

-- A key that is not there is `KeyError`, not a silent no-op.  CPython agrees.
#guard match (delIdx (.name "d") (.lit (.str "zz"))).2 with
       | .exn (.str "KeyError") _ => true | _ => false

-- Out of range on a list is `IndexError`.  CPython agrees.
#guard match (delIdx (.name "xs") (.lit (.int 5))).2 with
       | .exn (.str "IndexError") _ => true | _ => false

-- A `tuple` payload is immutable.
#guard match (delIdx (.name "t") (.lit (.int 0))).2 with
       | .exn (.str "TypeError") _ => true | _ => false

-- A boxed literal deletes; a C aggregate value still holes.
#guard match (delIdx (.listE [.lit (.int 1)]) (.lit (.int 0))).2 with
       | .normal _ => true | _ => false
#guard match (execStmt setIdxCtxC 50 setIdxHeap setIdxEnv
                (.delIndex (.listE [.lit (.int 1)]) (.lit (.int 0)))).2 with
       | .hole "delIndex:immutable-containers" => true | _ => false

private def mcallOn (recv : Expr) (m : String) (args : List Expr) : Heap × EResult :=
  evalExpr setIdxCtx 60 setIdxHeap setIdxEnv (.mcall recv m args)

-- `xs.append(3)` mutates the payload in place, and aliases see it.  CPython [1,2,3]
#guard match (mcallOn (.name "xs") "append" [.lit (.int 3)]).1[0]!.payload with
       | .list [.int 1, .int 2, .int 3] => true | _ => false

-- ... and bumps the version, so an iterator can tell.
#guard (mcallOn (.name "xs") "append" [.lit (.int 3)]).1[0]!.version == 1

-- `xs.pop()` returns the element AND shortens the receiver.  CPython 2, [1]
#guard match (mcallOn (.name "xs") "pop" []).2 with
       | .val (.int 2) => true | _ => false
#guard match (mcallOn (.name "xs") "pop" []).1[0]!.payload with
       | .list [.int 1] => true | _ => false

-- A pure builtin leaves the payload alone.
#guard match (mcallOn (.name "d") "get" [.lit (.str "a")]).2 with
       | .val (.int 1) => true | _ => false
#guard (mcallOn (.name "d") "get" [.lit (.str "a")]).1[1]!.version == 0

-- An ordinary instance has no payload, so nothing changed for it.
#guard match (mcallOn (.name "o") "append" [.lit (.int 3)]).2 with
       | .hole "mcall:Plain.append" => true | _ => false

-- §4, live iteration. `for v in xs: del xs[0]` on [1,2].
-- CPython sees one element and ends with [2]; a SNAPSHOT loop would see two. This is the
-- case §4 says must not survive boxing, because it is silently wrong the moment a
-- container can be mutated mid-loop.
private def shrinkLoop : Heap × Ctl :=
  execStmt setIdxCtx 300 setIdxHeap setIdxEnv
    (.forIn "v" (.name "xs") (.delIndex (.name "xs") (.lit (.int 0))))

#guard match shrinkLoop.1[0]!.payload with | .list [.int 2] => true | _ => false
-- Iterated once, not twice: the loop variable never reached the second element.
#guard match shrinkLoop.2 with
       | .normal ρ => (match ρ.get "v" with | .int 1 => true | _ => false)
       | _ => false

-- A dict mutated during iteration raises, which is what `Obj.version` is for.
-- CPython: RuntimeError: dictionary changed size during iteration.
#guard match (execStmt setIdxCtx 300 setIdxHeap setIdxEnv
                (.forIn "k" (.name "d")
                  (.setIndex (.name "d") (.lit (.str "c")) (.lit (.int 3))))).2 with
       | .exn (.str "RuntimeError") _ => true | _ => false

-- THE POINT OF THE WHOLE MIGRATION: a Python list literal is boxed, so `[1][0] = 9`
-- assigns instead of holing. Under a non-Python dialect the literal is still a value and
-- still holes, which is correct -- a C aggregate has no identity.
#guard match (setIdx (.listE [.lit (.int 1)]) (.lit (.int 0)) (.lit (.int 9))).2 with
       | .normal _ => true | _ => false
#guard match (execStmt setIdxCtxC 50 setIdxHeap setIdxEnv
                (.setIndex (.listE [.lit (.int 1)]) (.lit (.int 0)) (.lit (.int 9)))).2 with
       | .hole "setIndex:immutable-containers" => true | _ => false

/-! ## The container protocol on user instances, checked against CPython

`class Bag: def __contains__(self, k): return k == 1` -- `1 in Bag()` is `True`,
`2 in Bag()` is `False`, `2 not in Bag()` is `True`. A `__getitem__` that doubles its key,
a `__setitem__` that records `k + v` in a field, a `__delitem__` that records the key; and
`Plain`, which defines none of them, keeps exactly the holes it had. Boxed containers are
untouched by this path (`Ctx.dunderOn` is `none` on any payload), which the `aliasProg`
guards below keep checking. -/
private def dunderProg : Program :=
  { dialect := .python
  , funcs :=
    [ { name := "m.py:<module>.Bag.__contains__", params := ["k"]
      , body := .ret (.binop "==" (.name "k") (.lit (.int 1))) }
    , { name := "m.py:<module>.Bag.__getitem__", params := ["k"]
      , body := .ret (.binop "*" (.name "k") (.lit (.int 2))) }
    , { name := "m.py:<module>.Bag.__setitem__", params := ["k", "v"]
      , body := .setField (.name "self") "last" (.binop "+" (.name "k") (.name "v")) }
    , { name := "m.py:<module>.Bag.__delitem__", params := ["k"]
      , body := .setField (.name "self") "deleted" (.name "k") }
    , { name := "m.py:<module>.hit", params := []
      , body := .seq (.assign "b" (.alloc "Bag" []))
                     (.ret (.inOp false (.lit (.int 1)) (.name "b"))) }
    , { name := "m.py:<module>.miss", params := []
      , body := .seq (.assign "b" (.alloc "Bag" []))
                     (.ret (.inOp false (.lit (.int 2)) (.name "b"))) }
    , { name := "m.py:<module>.notIn", params := []
      , body := .seq (.assign "b" (.alloc "Bag" []))
                     (.ret (.inOp true (.lit (.int 2)) (.name "b"))) }
    , { name := "m.py:<module>.get", params := []
      , body := .seq (.assign "b" (.alloc "Bag" []))
                     (.ret (.index (.name "b") (.lit (.int 21)))) }
    , { name := "m.py:<module>.set", params := []
      , body := .seq (.assign "b" (.alloc "Bag" []))
               (.seq (.setIndex (.name "b") (.lit (.int 40)) (.lit (.int 2)))
                     (.ret (.field (.name "b") "last"))) }
    , { name := "m.py:<module>.del", params := []
      , body := .seq (.assign "b" (.alloc "Bag" []))
               (.seq (.delIndex (.name "b") (.lit (.int 7)))
                     (.ret (.field (.name "b") "deleted"))) }
    , { name := "m.py:<module>.plainIn", params := []
      , body := .seq (.assign "p" (.alloc "Plain" []))
                     (.ret (.inOp false (.lit (.int 1)) (.name "p"))) }
    , { name := "m.py:<module>.plainGet", params := []
      , body := .seq (.assign "p" (.alloc "Plain" []))
                     (.ret (.index (.name "p") (.lit (.int 1)))) }
    , { name := "m.py:<module>.plainSet", params := []
      , body := .seq (.assign "p" (.alloc "Plain" []))
                     (.setIndex (.name "p") (.lit (.int 1)) (.lit (.int 2))) }
    , { name := "m.py:<module>.plainDel", params := []
      , body := .seq (.assign "p" (.alloc "Plain" []))
                     (.delIndex (.name "p") (.lit (.int 1))) }
    -- `in` on a BOXED list still takes the structural path: `2 in [1, 2]`.
    , { name := "m.py:<module>.boxedIn", params := []
      , body := .seq (.assign "xs" (.listE [.lit (.int 1), .lit (.int 2)]))
                     (.ret (.inOp false (.lit (.int 2)) (.name "xs"))) } ] }

-- `1 in Bag()`      CPython True
#guard match runFunc dunderProg 200 "m.py:<module>.hit" [] with
       | .val (.bool true) => true | _ => false
-- `2 in Bag()`      CPython False
#guard match runFunc dunderProg 200 "m.py:<module>.miss" [] with
       | .val (.bool false) => true | _ => false
-- `2 not in Bag()`  CPython True -- the negation is of `__contains__`'s truthiness
#guard match runFunc dunderProg 200 "m.py:<module>.notIn" [] with
       | .val (.bool true) => true | _ => false
-- `Bag()[21]`       CPython 42
#guard match runFunc dunderProg 200 "m.py:<module>.get" [] with
       | .val (.int 42) => true | _ => false
-- `b[40] = 2; b.last`  CPython 42 -- `__setitem__` ran on THIS instance
#guard match runFunc dunderProg 200 "m.py:<module>.set" [] with
       | .val (.int 42) => true | _ => false
-- `del b[7]; b.deleted`  CPython 7
#guard match runFunc dunderProg 200 "m.py:<module>.del" [] with
       | .val (.int 7) => true | _ => false
-- A class WITHOUT the dunder keeps the hole it had: nothing is guessed.
#guard match runFunc dunderProg 200 "m.py:<module>.plainIn" [] with
       | .hole "in:non-container" => true | _ => false
#guard match runFunc dunderProg 200 "m.py:<module>.plainGet" [] with
       | .hole "index:unsupported" => true | _ => false
#guard match runFunc dunderProg 200 "m.py:<module>.plainSet" [] with
       | .hole "setIndex:immutable-containers" => true | _ => false
#guard match runFunc dunderProg 200 "m.py:<module>.plainDel" [] with
       | .hole "delIndex:immutable-containers" => true | _ => false
-- `2 in [1, 2]` on a boxed list: True, through the structural path.
#guard match runFunc dunderProg 200 "m.py:<module>.boxedIn" [] with
       | .val (.bool true) => true | _ => false

/-! ## The switchover: containers have identity

`docs/boxed-containers.md`. A Python list or dict literal now allocates, so two names can
refer to one container and a write through either is visible through the other. This is
the whole point of the migration, and it is the case Core could not express at all
before: `Val.list` was a value, so `b = a` copied it and `b[0] = 9` was a hole.

Every expectation is CPython's, executed. -/
/-! ## A receiver followed by nothing but collectors, checked against CPython

`class C: def f(self, *a, **k): return (a, k)`. The exporter strips `self` and records
`receiverName := some "self"` because `**k` could otherwise swallow a `self=` keyword.
Every expected value below is CPython's. -/
private def collProg : Program :=
  { dialect := .python
  , funcs :=
    [ { name := "m.py:<module>.C.f", params := ["a", "k"], vararg := some "a", kwarg := some "k"
      , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := []
                                , isMethod := some true, receiverName := some "self" }
      , body := .ret (.tupleE [.name "a", .name "k"]) } ] }
private def collCtx : Ctx := { dialect := .python, table := collProg.table }
private def collCall (args : List Expr) : Heap × EResult :=
  evalExpr collCtx 60 [{ cls := "C", fields := [] }] [("o", .ref 0)] (.mcall (.name "o") "f" args)

-- o.f(1, 2, x=3)   CPython ((1, 2), {'x': 3}) -- `self` is the receiver, not consumed by `*a`
#guard match (collCall [.lit (.int 1), .lit (.int 2), .kwargE "x" (.lit (.int 3))]).2 with
       | .val (.tuple [.tuple [.int 1, .int 2], .dict [(.str "x", .int 3)]]) => true | _ => false
-- o.f()            CPython ((), {})
#guard match (collCall []).2 with
       | .val (.tuple [.tuple [], .dict []]) => true | _ => false
-- o.f(self=1)      CPython TypeError: f() got multiple values for argument 'self'
#guard match (collCall [.kwargE "self" (.lit (.int 1))]).2 with
       | .exn (.str "TypeError") => true | _ => false
-- o.f(1, self=2)   CPython TypeError (same reason; the positional went to `*a`)
#guard match (collCall [.lit (.int 1), .kwargE "self" (.lit (.int 2))]).2 with
       | .exn (.str "TypeError") => true | _ => false

private def aliasProg : Program :=
  { dialect := .python
  , funcs :=
    [ { name := "alias", params := []
      , body :=
          .seq (.assign "a" (.listE [.lit (.int 1), .lit (.int 2)]))
          (.seq (.assign "b" (.name "a"))
          (.seq (.setIndex (.name "b") (.lit (.int 0)) (.lit (.int 9)))
                (.ret (.index (.name "a") (.lit (.int 0)))))) }
    , { name := "appendThroughAlias", params := []
      , body :=
          .seq (.assign "a" (.listE [.lit (.int 1)]))
          (.seq (.assign "b" (.name "a"))
          (.seq (.expr (.mcall (.name "b") "append" [.lit (.int 7)]))
                (.ret (.index (.name "a") (.lit (.int 1)))))) }
    , { name := "dictAlias", params := []
      , body :=
          .seq (.assign "d" (.dictE []))
          (.seq (.assign "e" (.name "d"))
          (.seq (.setIndex (.name "e") (.lit (.str "k")) (.lit (.int 5)))
                (.ret (.index (.name "d") (.lit (.str "k")))))) }
    , { name := "equalButNotIdentical", params := []
      , body :=
          .seq (.assign "a" (.listE [.lit (.int 1)]))
          (.seq (.assign "b" (.listE [.lit (.int 1)]))
                (.ret (.binop "==" (.name "a") (.name "b")))) }
    , { name := "identity", params := []
      , body :=
          .seq (.assign "a" (.listE [.lit (.int 1)]))
          (.seq (.assign "b" (.listE [.lit (.int 1)]))
                (.ret (.isOp false (.name "a") (.name "b")))) } ] }

-- `a = [1,2]; b = a; b[0] = 9; a[0]`  -- CPython 9
#guard match runFunc aliasProg 400 "alias" [] with
       | .val (.int 9) => true | _ => false
-- `a = [1]; b = a; b.append(7); a[1]`  -- CPython 7
#guard match runFunc aliasProg 400 "appendThroughAlias" [] with
       | .val (.int 7) => true | _ => false
-- `d = {}; e = d; e["k"] = 5; d["k"]`  -- CPython 5
#guard match runFunc aliasProg 400 "dictAlias" [] with
       | .val (.int 5) => true | _ => false
-- Two distinct lists with equal contents are `==` (this is `Val.eqPy` through the heap)
-- but not `is`. Before boxing Core could not tell these apart -- the case
-- `STRATEGY.md` §31/§34 records against `_HashedTuple`.
#guard match runFunc aliasProg 400 "equalButNotIdentical" [] with
       | .val (.bool true) => true | _ => false
#guard match runFunc aliasProg 400 "identity" [] with
       | .val (.bool false) => true | _ => false

/-! ## Slices, checked against CPython

`xs = [1, 2, 3, 4, 5]`, boxed. Every expected value below is CPython's, and the failure
cases are CPython's exceptions by name. A slice read is a fresh allocation, so its result
is a `Val.ref` to a NEW heap cell, whose payload is what is checked. -/
private def sliceHeap : Heap :=
  [ { cls := "list", fields := [], payload := .list [.int 1, .int 2, .int 3, .int 4, .int 5] } ]
private def sliceEnv : Env :=
  [("xs", .ref 0), ("t", .tuple [.int 1, .int 2, .int 3]), ("s", .str "hello")]
private def sU : Expr := .lit .unit
private def sI (i : Int) : Expr := .lit (.int i)
private def slRead (recv lo hi st : Expr) : Heap × EResult :=
  evalExpr setIdxCtx 80 sliceHeap sliceEnv (.slice recv lo hi st)
private def slList (r : Heap × EResult) : Option (List Val) :=
  match r.2 with
  | .val (.ref k) =>
      match r.1.payload k with
      | .list vs => some vs
      | _        => none
  | _ => none
private def slStmt (st : Stmt) : Heap × Ctl := execStmt setIdxCtx 120 sliceHeap sliceEnv st
private def slAt0 (r : Heap × Ctl) : Payload := r.1.payload 0

-- xs[1:]     CPython [2, 3, 4, 5]
#guard match slList (slRead (.name "xs") (sI 1) sU sU) with
       | some [.int 2, .int 3, .int 4, .int 5] => true | _ => false
-- xs[:-1]    CPython [1, 2, 3, 4]
#guard match slList (slRead (.name "xs") sU (sI (-1)) sU) with
       | some [.int 1, .int 2, .int 3, .int 4] => true | _ => false
-- xs[::-1]   CPython [5, 4, 3, 2, 1]
#guard match slList (slRead (.name "xs") sU sU (sI (-1))) with
       | some [.int 5, .int 4, .int 3, .int 2, .int 1] => true | _ => false
-- xs[::2]    CPython [1, 3, 5]
#guard match slList (slRead (.name "xs") sU sU (sI 2)) with
       | some [.int 1, .int 3, .int 5] => true | _ => false
-- xs[5:]     CPython []  (a start past the end is empty, not an error)
#guard match slList (slRead (.name "xs") (sI 5) sU sU) with
       | some [] => true | _ => false
-- xs[-2:]    CPython [4, 5]
#guard match slList (slRead (.name "xs") (sI (-2)) sU sU) with
       | some [.int 4, .int 5] => true | _ => false
-- xs[3:1]    CPython []  (reversed bounds with a positive step)
#guard match slList (slRead (.name "xs") (sI 3) (sI 1) sU) with
       | some [] => true | _ => false
-- xs[::0]    CPython ValueError: slice step cannot be zero
#guard match (slRead (.name "xs") sU sU (sI 0)).2 with
       | .exn (.str "ValueError") => true | _ => false
-- xs["a":]   CPython TypeError: slice indices must be integers or None
#guard match (slRead (.name "xs") (.lit (.str "a")) sU sU).2 with
       | .exn (.str "TypeError") => true | _ => false
-- The slice is a COPY: the original is untouched by the read.
#guard match (slRead (.name "xs") (sI 1) sU sU).1.payload 0 with
       | .list [.int 1, .int 2, .int 3, .int 4, .int 5] => true | _ => false
-- t[1:]      CPython (2, 3) -- a tuple slice is a tuple value, not an allocation
#guard match (slRead (.name "t") (sI 1) sU sU).2 with
       | .val (.tuple [.int 2, .int 3]) => true | _ => false
-- s[1:3]     CPython 'el'
#guard match (slRead (.name "s") (sI 1) (sI 3) sU).2 with
       | .val (.str "el") => true | _ => false
-- s[::-1]    CPython 'olleh'
#guard match (slRead (.name "s") sU sU (sI (-1))).2 with
       | .val (.str "olleh") => true | _ => false

-- del xs[0:1]        CPython [2, 3, 4, 5]
#guard match slAt0 (slStmt (.delSlice (.name "xs") (sI 0) (sI 1) sU)) with
       | .list [.int 2, .int 3, .int 4, .int 5] => true | _ => false
-- del xs[::2]        CPython [2, 4]
#guard match slAt0 (slStmt (.delSlice (.name "xs") sU sU (sI 2))) with
       | .list [.int 2, .int 4] => true | _ => false
-- xs[0:1] = [9, 8]   CPython [9, 8, 2, 3, 4, 5]  (a unit-step assignment may resize)
#guard match slAt0 (slStmt (.setSlice (.name "xs") (sI 0) (sI 1) sU
                             (.listE [sI 9, sI 8]))) with
       | .list [.int 9, .int 8, .int 2, .int 3, .int 4, .int 5] => true | _ => false
-- xs[3:1] = [9]      CPython [1, 2, 3, 9, 4, 5]  (reversed bounds insert at `lower`)
#guard match slAt0 (slStmt (.setSlice (.name "xs") (sI 3) (sI 1) sU (.listE [sI 9]))) with
       | .list [.int 1, .int 2, .int 3, .int 9, .int 4, .int 5] => true | _ => false
-- xs[::2] = [7, 7, 7]  CPython [7, 2, 7, 4, 7]
#guard match slAt0 (slStmt (.setSlice (.name "xs") sU sU (sI 2)
                             (.listE [sI 7, sI 7, sI 7]))) with
       | .list [.int 7, .int 2, .int 7, .int 4, .int 7] => true | _ => false
-- xs[::2] = [7]      CPython ValueError: attempt to assign sequence of size 1 to
--                    extended slice of size 3
#guard match (slStmt (.setSlice (.name "xs") sU sU (sI 2) (.listE [sI 7]))).2 with
       | .exn (.str "ValueError") _ => true | _ => false
-- xs[0:1] = 5        CPython TypeError: can only assign an iterable
#guard match (slStmt (.setSlice (.name "xs") (sI 0) (sI 1) sU (sI 5))).2 with
       | .exn (.str "TypeError") _ => true | _ => false

/-! ## Value dunders, checked against CPython

`class P: __init__(x), __eq__, __lt__`; `class C: __len__ → 3`; `class Z: __len__ → 0`;
`class H: __hash__ → 7`, `__str__ → "h"`; `class Q:` (nothing). Each expectation is what
CPython 3.11 prints. -/
private def valueDunderProg : Program :=
  { dialect := .python
  , funcs :=
    [ { name := "d.py:<module>.P.__init__", params := ["x"]
      , body := .setField (.name "self") "x" (.name "x") }
    , { name := "d.py:<module>.P.__eq__", params := ["o"]
      , body := .ret (.binop "==" (.field (.name "self") "x") (.field (.name "o") "x")) }
    , { name := "d.py:<module>.P.__lt__", params := ["o"]
      , body := .ret (.binop "<" (.field (.name "self") "x") (.field (.name "o") "x")) }
    , { name := "d.py:<module>.C.__len__", params := [], body := .ret (.lit (.int 3)) }
    , { name := "d.py:<module>.Z.__len__", params := [], body := .ret (.lit (.int 0)) }
    , { name := "d.py:<module>.H.__hash__", params := [], body := .ret (.lit (.int 7)) }
    , { name := "d.py:<module>.H.__str__", params := [], body := .ret (.lit (.str "h")) }
    , { name := "d.py:<module>.Q.__init__", params := [], body := .skip }
    , { name := "eqTrue", params := []
      , body := .ret (.binop "==" (.alloc "P" [.lit (.int 1)]) (.alloc "P" [.lit (.int 1)])) }
    , { name := "eqFalse", params := []
      , body := .ret (.binop "==" (.alloc "P" [.lit (.int 1)]) (.alloc "P" [.lit (.int 2)])) }
    , { name := "neFalse", params := []
      , body := .ret (.binop "!=" (.alloc "P" [.lit (.int 1)]) (.alloc "P" [.lit (.int 1)])) }
    , { name := "ltTrue", params := []
      , body := .ret (.binop "<" (.alloc "P" [.lit (.int 1)]) (.alloc "P" [.lit (.int 2)])) }
    , { name := "geHole", params := []   -- no `__ge__`: stays the hole it was
      , body := .ret (.binop ">=" (.alloc "P" [.lit (.int 1)]) (.alloc "P" [.lit (.int 2)])) }
    , { name := "lenC", params := [], body := .ret (.call "len" [.alloc "C" []]) }
    , { name := "boolC", params := [], body := .ret (.call "bool" [.alloc "C" []]) }
    , { name := "boolZ", params := [], body := .ret (.call "bool" [.alloc "Z" []]) }
    , { name := "hashH", params := [], body := .ret (.call "hash" [.alloc "H" []]) }
    , { name := "strH", params := [], body := .ret (.call "str" [.alloc "H" []]) }
    , { name := "identityQ", params := []
      , body := .ret (.binop "==" (.alloc "Q" []) (.alloc "Q" [])) }
    , { name := "lenQ", params := [], body := .ret (.call "len" [.alloc "Q" []]) } ] }

-- `P(1) == P(1)`  -- CPython True (through `__eq__`; identity would say False)
#guard match runFunc valueDunderProg 200 "eqTrue" [] with | .val (.bool true) => true | _ => false
-- `P(1) == P(2)`  -- CPython False
#guard match runFunc valueDunderProg 200 "eqFalse" [] with | .val (.bool false) => true | _ => false
-- `P(1) != P(1)`  -- CPython False (default `__ne__` negates `__eq__`)
#guard match runFunc valueDunderProg 200 "neFalse" [] with | .val (.bool false) => true | _ => false
-- `P(1) < P(2)`   -- CPython True
#guard match runFunc valueDunderProg 200 "ltTrue" [] with | .val (.bool true) => true | _ => false
-- `P(1) >= P(2)`  -- CPython TypeError ('>=' not supported); Core keeps the hole, not a guess
#guard match runFunc valueDunderProg 200 "geHole" [] with | .hole _ => true | _ => false
-- `len(C())`      -- CPython 3
#guard match runFunc valueDunderProg 200 "lenC" [] with | .val (.int 3) => true | _ => false
-- `bool(C())`     -- CPython True (no `__bool__`, so `__len__() != 0`)
#guard match runFunc valueDunderProg 200 "boolC" [] with | .val (.bool true) => true | _ => false
-- `bool(Z())`     -- CPython False
#guard match runFunc valueDunderProg 200 "boolZ" [] with | .val (.bool false) => true | _ => false
-- `hash(H())`     -- CPython 7;  `str(H())` -- 'h'
#guard match runFunc valueDunderProg 200 "hashH" [] with | .val (.int 7) => true | _ => false
#guard match runFunc valueDunderProg 200 "strH" [] with | .val (.str "h") => true | _ => false
-- `Q() == Q()`    -- CPython False: no `__eq__`, so identity, and these are two objects
#guard match runFunc valueDunderProg 200 "identityQ" [] with | .val (.bool false) => true | _ => false
-- `len(Q())`      -- CPython TypeError; Core has no `len` on an instance without `__len__`
--                    and says so (`call:len`), which is the pre-existing behaviour.
#guard match runFunc valueDunderProg 200 "lenQ" [] with | .hole _ => true | _ => false

/-! ## JavaScript arrays and strings

The JS frontend lowers `[a, b]` to `__ecma.Array.factory()` followed by `.push(a)`,
`.push(b)` -- a constructor plus in-place mutation, which is exactly the boxed-container
shape. `push` returns the NEW LENGTH where Python's `append` returns `None`, which is why
`.javascript` has its own `Stdlib.methodCore` table rather than borrowing Python's. Every
expectation below is Node's. -/
private def jsProg : Program :=
  { dialect := .javascript
  , funcs :=
    [ { name := "build", params := []
      , body :=
          .seq (.assign "xs" (.listE []))
          (.seq (.expr (.mcall (.name "xs") "push" [.lit (.int 1)]))
          (.seq (.assign "n" (.mcall (.name "xs") "push" [.lit (.int 2)]))
                (.ret (.binop "+" (.name "n")
                         (.binop "*" (.lit (.int 10)) (.field (.name "xs") "length")))))) }
    , { name := "oob", params := []
      , body := .seq (.assign "xs" (.listE [.lit (.int 1)]))
                     (.ret (.index (.name "xs") (.lit (.int 5)))) }
    , { name := "strIdx", params := []
      , body := .ret (.index (.lit (.str "xy")) (.lit (.int 0))) }
    , { name := "strLen", params := []
      , body := .ret (.field (.lit (.str "xy")) "length") }
      -- `o = {a: 1}; o.b = 2; o.a + o.b * 10 + (o.c === undefined ? 100 : 0)`  -- Node: 121
    , { name := "objLit", params := []
      , body :=
          .seq (.assign "o" (.dictE [(.lit (.str "a"), .lit (.int 1))]))
          (.seq (.setField (.name "o") "b" (.lit (.int 2)))
                (.ret (.binop "+" (.field (.name "o") "a")
                         (.binop "+" (.binop "*" (.field (.name "o") "b") (.lit (.int 10)))
                            (.cond (.binop "==" (.field (.name "o") "c") (.lit .unit))
                               (.lit (.int 100)) (.lit (.int 0))))))) }
      -- `xs = [1, 2]; xs.foo`  -- Node: undefined
    , { name := "arrMiss", params := []
      , body := .seq (.assign "xs" (.listE [.lit (.int 1), .lit (.int 2)]))
                     (.ret (.field (.name "xs") "foo")) } ] }

-- `xs = []; xs.push(1); n = xs.push(2); n + 10 * xs.length`  -- Node: 2 + 20 = 22
#guard match runFunc jsProg 300 "build" [] with | .val (.int 22) => true | _ => false
-- Out of range on an array is `undefined`, not an exception.  -- Node: undefined
#guard match runFunc jsProg 300 "oob" [] with | .val .unit => true | _ => false
-- `"xy"[0]` is `"x"`; `"xy".length` is 2.
#guard match runFunc jsProg 300 "strIdx" [] with | .val (.str "x") => true | _ => false
#guard match runFunc jsProg 300 "strLen" [] with | .val (.int 2) => true | _ => false
-- An object literal's own keys are its properties; a missing one is `undefined`, and a
-- property write lands in the literal, not beside it.  -- Node: 121
#guard match runFunc jsProg 300 "objLit" [] with | .val (.int 121) => true | _ => false
#guard match runFunc jsProg 300 "arrMiss" [] with | .val .unit => true | _ => false

-- UTF-16 units: `"😀".length` is 2 and its first unit is a lone surrogate.
#guard "xy".jsLength == 2
#guard "😀".jsLength == 2
#guard "xy".utf16At 0 == some 120
#guard "xy".utf16At 5 == none
#guard "xy".utf16At (-1) == none
#guard ("😀".utf16At 0).any Nat.isUTF16Surrogate

/-! ## Go: tuple assignment and the `for` forms, checked against `go run`

These are the Core shapes `cartographer/export_ast.sc`'s `goTupleAssign` and `forStmt`
emit for Go source, run under `.go`. Every expectation is `go1.20.6`'s output for the
program in the comments (`.tmp_gospec/main.go` while this was written).

* Go spec, "Assignment statements": "The assignment proceeds in two phases. First, the
  operands of index expressions and pointer indirections [...] on the left and the
  expressions on the right are all evaluated in the usual order. Second, the assignments
  are carried out in left-to-right order." -- hence the temporaries: `a, b = b, a` swaps.
* Go spec, "For statements": "The iteration may be controlled by a single condition, a
  "for" clause, or a "range" clause." [...] "If the condition is absent, it is
  equivalent to the boolean value true." -/
private def goProg : Program :=
  { dialect := .go
  , funcs :=
    -- a, b := 1, 2; a, b = b, a; return a*10 + b        -- go: 21
    [ { name := "swap", params := []
      , body :=
          .seq (.assign "a" (.lit (.int 1)))
          (.seq (.assign "b" (.lit (.int 2)))
          (.seq (.assign "$t0" (.name "b"))
          (.seq (.assign "$t1" (.name "a"))
          (.seq (.assign "a" (.name "$t0"))
          (.seq (.assign "b" (.name "$t1"))
                (.ret (.binop "+" (.binop "*" (.name "a") (.lit (.int 10))) (.name "b")))))))) }
    -- func pair() (int, int) { return 3, 4 }; x, y := pair(); return x*10 + y   -- go: 34
    , { name := "pair", params := []
      , body := .ret (.tupleE [.lit (.int 3), .lit (.int 4)]) }
    , { name := "destructure", params := []
      , body :=
          .seq (.assign "$t" (.call "pair" []))
          (.seq (.assign "x" (.index (.name "$t") (.lit (.int 0))))
          (.seq (.assign "y" (.index (.name "$t") (.lit (.int 1))))
                (.ret (.binop "+" (.binop "*" (.name "x") (.lit (.int 10))) (.name "y"))))) }
    -- i := 0; for i < 3 { i = i + 1 }; return i          -- go: 3
    , { name := "cond", params := []
      , body :=
          .seq (.assign "i" (.lit (.int 0)))
          (.seq (.loop (.binop "<" (.name "i") (.lit (.int 3)))
                       (.assign "i" (.binop "+" (.name "i") (.lit (.int 1)))))
                (.ret (.name "i"))) }
    -- i := 0; for { i = i + 2; if i > 4 { break } }; return i   -- go: 6
    , { name := "forever", params := []
      , body :=
          .seq (.assign "i" (.lit (.int 0)))
          (.seq (.loop (.lit (.bool true))
                       (.seq (.assign "i" (.binop "+" (.name "i") (.lit (.int 2))))
                             (.ifte (.binop ">" (.name "i") (.lit (.int 4))) .brk .skip)))
                (.ret (.name "i"))) } ] }

#guard match runFunc goProg 300 "swap" [] with | .val (.int 21) => true | _ => false
#guard match runFunc goProg 300 "destructure" [] with | .val (.int 34) => true | _ => false
#guard match runFunc goProg 300 "cond" [] with | .val (.int 3) => true | _ => false
#guard match runFunc goProg 300 "forever" [] with | .val (.int 6) => true | _ => false

end Autoform.Core
