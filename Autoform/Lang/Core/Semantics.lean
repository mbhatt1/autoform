import Autoform.Lang.Core.Syntax
import Autoform.Lang.Core.Numeric
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

/-- Integer division under a dialect. -/
def Dialect.idiv : Dialect → Int → Int → Int
  | .python, a, b => Int.fdiv a b
  | .cLike,  a, b => Int.tdiv a b

/-- Integer remainder under a dialect. -/
def Dialect.imod : Dialect → Int → Int → Int
  | .python, a, b => Int.fmod a b
  | .cLike,  a, b => Int.tmod a b


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
      | .cLike  => match (d.toFConfig).ofInt n with   -- C promotes, and may round
                   | .ok x => Fl.cmpv x y
                   | _     => none
  | .float x, .int n   =>
      (match d with
       | .python => Fl.cmpIntv n x
       | .cLike  => match (d.toFConfig).ofInt n with
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
                   | _   => fc.pyMod x y)
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
  | "==", x, y           => .val (.bool (Val.beq x y))
  | "!=", x, y           => .val (.bool (!Val.beq x y))
  -- Reached only when the left operand did not decide the result, so the value
  -- of the expression is the RIGHT operand under value semantics.
  | "&&", _, y           => .val (if d.boolOpsAreValues then y else .bool y.truthy)
  | "||", _, y           => .val (if d.boolOpsAreValues then y else .bool y.truthy)
  | _, _, _              => .hole s!"binop:{op}"

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
  -- Negation goes through `NumConfig` for the same reason the binary operators do:
  -- `-INT_MIN` is not representable, so under a fixed-width dialect it must wrap, trap,
  -- or become a hole — never the unrepresentable number. This path was left unchecked
  -- when `Numeric` was first wired in, and `Autoform/Refine.lean` caught it.
  | "-", .int x => numToE ((d.toNumConfig).neg x)
  -- Float negation is a sign-bit flip: exact, no rounding, and correct on `-0.0` and NaN
  -- where "subtract from zero" would not be (`0.0 - 0.0 = 0.0`, but `-(0.0) = -0.0`).
  | "-", .float f => .val (.float f.neg)
  | "!", x      => .val (.bool (!x.truthy))
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
  | _, _        => .hole s!"unop:{op}"

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

/-- Everything the interpreter needs: the callable functions and the source dialect. -/
structure Ctx where
  dialect : Dialect
  table   : FuncTable
  /-- Classes whose base is a builtin type — see `Program.builtinBases`. -/
  builtinBases : List (String × BuiltinBase) := []
  /-- Heap address of the module-level bindings frame. Globals must be mutable and must
  outlive any single call, so they live on the heap rather than in `Env`. -/
  globals : Ref := 0

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

/-- Resolve a method on a class: prefer `Cls.meth`, else any `.meth`. -/
def Ctx.resolveMethod (ctx : Ctx) (cls meth : String) : Option Func :=
  match ctx.table.filter (fun p => p.1.endsWith ("." ++ cls ++ "." ++ meth)) with
  | (_, f) :: _ => some f
  | []          => ctx.resolve meth

/-- Does this class define this method *itself*? Unlike `resolveMethod` there is no
free-function fallback, so a global `__eq__` cannot be mistaken for a class's own. -/
def Ctx.classDefines (ctx : Ctx) (cls meth : String) : Bool :=
  ctx.table.any (fun p => p.1.endsWith ("." ++ cls ++ "." ++ meth))

/-- The builtin base of a class, if the exporter recorded one. -/
def Ctx.builtinBase (ctx : Ctx) (cls : String) : Option BuiltinBase :=
  match ctx.builtinBases.find? (·.1 == cls) with
  | some (_, b) => some b
  | none        => none

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
          | (h₂, .val y) => (h₂, applyBinop ctx.dialect op x y)
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
            -- `is` is reference identity for objects, structural for immediates.
            let same := match x, y with
                        | .ref p, .ref q => p == q
                        | p, q           => Val.beq p q
            (h₂, .val (.bool (if neg then !same else same)))
        | (h₂, r) => (h₂, r)
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .inOp neg a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val x) =>
        match evalExpr ctx n h₁ ρ b with
        | (h₂, .val c) =>
            match valIn x c with
            | .val (.bool r) => (h₂, .val (.bool (if neg then !r else r)))
            | r              => (h₂, r)
        | (h₂, r) => (h₂, r)
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .index a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val c) =>
        match evalExpr ctx n h₁ ρ b with
        | (h₂, .val k) =>
          -- `A((0,))[0]` is `0` in CPython for `class A(tuple)`.
          match c.unbuiltin, k with
          | .list vs, .int i =>
              if hh : i.toNat < vs.length then (h₂, .val (vs[i.toNat]))
              else (h₂, .exn (.str "IndexError"))
          | .tuple vs, .int i =>
              if hh : i.toNat < vs.length then (h₂, .val (vs[i.toNat]))
              else (h₂, .exn (.str "IndexError"))
          | .dict kvs, key =>
              match kvs.find? (fun kv => Val.beq kv.1 key) with
              | some (_, v) => (h₂, .val v)
              | none        => (h₂, .exn (.str "KeyError"))
          | _, _ => (h₂, .hole "index:unsupported")
        | (h₂, r) => (h₂, r)
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
                           | none        => (h₁, .val .unit)
        | none => (h₁, .val .unit)
      | (h₁, .val _)        => (h₁, .hole s!"field:{f}:non-object")
      | (h₁, r)             => (h₁, r)
  | n+1, h, ρ, .listE es =>
      match evalList ctx n h ρ es with
      | (h₁, .inr vs) => (h₁, .val (.list vs))
      | (h₁, .inl r)  => (h₁, r)
  | n+1, h, ρ, .tupleE es =>
      match evalList ctx n h ρ es with
      | (h₁, .inr vs) => (h₁, .val (.tuple vs))
      | (h₁, .inl r)  => (h₁, r)
  | n+1, h, ρ, .dictE kvs =>
      match evalPairs ctx n h ρ kvs with
      | (h₁, .inr ps) => (h₁, .val (.dict ps))
      | (h₁, .inl r)  => (h₁, r)
  | n+1, h, ρ, .call f args =>
      match evalList ctx n h ρ args with
      | (h₁, .inl r)  => (h₁, r)
      | (h₁, .inr vs) =>
        match ctx.resolve f with
        | some fn => applyFunc ctx n h₁ fn none vs
        | none    =>
          -- Not a statically known function: it may be a function value or closure held
          -- in a variable (`f = g; f(x)`, decorators, callbacks).
          match ρ.get f with
          | .fn g      => match ctx.resolve g with
                          | some fn => applyFunc ctx n h₁ fn none vs
                          | none    => (h₁, .hole s!"call:{g}")
          | .clos g cap => match ctx.resolve g with
                          | some fn => applyClosure ctx n h₁ fn cap vs
                          | none    => (h₁, .hole s!"call:{g}")
          | _          =>
            -- Modelled stdlib is consulted LAST, so a user function of the same name
            -- always wins. `builtin` returns `none` for anything it cannot model
            -- faithfully, which falls through to a visible hole.
            match Stdlib.builtin ctx.dialect h₁ f vs with
            | some (h₂, r) => (h₂, r)
            | none         => (h₁, .hole s!"call:{f}")
  | n+1, h, ρ, .mcall recv m args =>
      match evalExpr ctx n h ρ recv with
      | (h₁, .val (.ref r)) =>
        match evalList ctx n h₁ ρ args with
        | (h₂, .inl e)  => (h₂, e)
        | (h₂, .inr vs) =>
          match h₂.get r with
          | none   => (h₂, .hole "mcall:dangling-ref")
          | some o =>
            match ctx.resolveMethod o.cls m with
            | none    => (h₂, .hole s!"mcall:{o.cls}.{m}")
            | some fn =>
              if o.captured.isEmpty then applyFunc ctx n h₂ fn (some (.ref r)) vs
              else applyClosure ctx n h₂ fn (("self", .ref r) :: o.captured) vs
      | (h₁, .val (.bobj bcls pay)) =>
        match evalList ctx n h₁ ρ args with
        | (h₂, .inl e)  => (h₂, e)
        | (h₂, .inr vs) =>
          -- Method dispatch on a builtin-based instance: the class's own methods first
          -- (`self` is bound to the whole instance, so `self` still compares as the
          -- builtin), then the builtin's own methods on the payload.
          if ctx.classDefines bcls m then
            match ctx.resolveMethod bcls m with
            | some fn => applyFunc ctx n h₂ fn (some (.bobj bcls pay)) vs
            | none    => (h₂, .hole s!"mcall:{bcls}.{m}")
          else
            match Stdlib.method ctx.dialect h₂ pay m vs with
            | some (h₃, .pure r)       => (h₃, r)
            | some (h₃, .mutating _ _) => (h₃, .hole s!"mcall:{m}:unboxed-container")
            | none                     => (h₂, .hole s!"mcall:{bcls}.{m}")
      | (h₁, .val recv) =>
        match evalList ctx n h₁ ρ args with
        | (h₂, .inl e)  => (h₂, e)
        | (h₂, .inr vs) =>
          match Stdlib.method ctx.dialect h₂ recv m vs with
          | some (h₃, .pure r)       => (h₃, r)
          -- A mutating container method cannot be honoured while containers are values:
          -- writing back through the receiver *expression* updates a temporary, because
          -- the CPG has already desugared `self.d.pop(k)` into `t = self.d; t.pop(k)`.
          -- An honest hole until containers are boxed (see docs/boxed-containers.md).
          | some (h₃, .mutating _ _) => (h₃, .hole s!"mcall:{m}:unboxed-container")
          | none                     => (h₂, .hole s!"mcall:{m}:non-object")
      | (h₁, r)      => (h₁, r)
  | n+1, h, ρ, .alloc cls args =>
      match evalList ctx n h ρ args with
      | (h₁, .inl r)  => (h₁, r)
      | (h₁, .inr vs) =>
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
          match applyFunc ctx n h₂ fn (some (.ref r)) vs with
          | (h₃, .val _)  => (h₃, .val (.ref r))
          | (h₃, .hole l) => (h₃, .hole l)
          | (h₃, e)       => (h₃, e)

/-- Apply a resolved function, optionally with a receiver bound to `self`. -/
def applyFunc (ctx : Ctx) : Nat → Heap → Func → Option Val → List Val → Heap × EResult
  | 0,   h, _,  _,     _  => (h, .outOfFuel)
  | n+1, h, fn, self?, vs =>
      let base : Env := match self? with
                        | some s => [("self", s)]
                        | none   => []
      let ρ := (fn.params.zip vs).foldl (fun e (x, v) => e.set x v) base
      match execStmt ctx n h ρ fn.body with
      | (h₁, .ret v)    => (h₁, .val v)
      | (h₁, .normal _) => (h₁, .val .unit)
      | (h₁, .exn v)    => (h₁, .exn v)
      | (h₁, .hole l)   => (h₁, .hole l)
      | (h₁, .outOfFuel)=> (h₁, .outOfFuel)
      | (h₁, _)         => (h₁, .hole "call:stray-control-flow")

/-- Apply a closure: the captured bindings form the base environment, then parameters
shadow them.

Capture is by value. Reads of enclosing variables therefore work, which covers decorators
and factory functions; a `nonlocal` **write** would need the binding to be a shared
mutable cell, so the transpiler keeps it as an explicit hole rather than pretending. -/
def applyClosure (ctx : Ctx) : Nat → Heap → Func → List (String × Val) → List Val →
    Heap × EResult
  | 0,   h, _,  _,   _  => (h, .outOfFuel)
  | n+1, h, fn, cap, vs =>
      let base : Env := cap
      let ρ : Env := (fn.params.zip vs).foldl (fun (e : Env) (x, v) => Env.set e x v) base
      match execStmt ctx n h ρ fn.body with
      | (h₁, .ret v)     => (h₁, .val v)
      | (h₁, .normal _)  => (h₁, .val .unit)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
      | (h₁, _)          => (h₁, .hole "call:stray-control-flow")

/-- Evaluate a list of expressions left to right, short-circuiting on the first
non-value. -/
def evalList (ctx : Ctx) : Nat → Heap → Env → List Expr → Heap × Sum EResult (List Val)
  | 0,   h, _, _       => (h, .inl .outOfFuel)
  | _+1, h, _, []      => (h, .inr [])
  | n+1, h, ρ, a :: as =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val v) =>
        match evalList ctx n h₁ ρ as with
        | (h₂, .inr vs) => (h₂, .inr (v :: vs))
        | (h₂, .inl r)  => (h₂, .inl r)
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
        match evalExpr ctx n h₁ ρ v with
        | (h₂, .val vv)    => (h₂.setField addr f vv, .normal ρ)
        | (h₂, .exn e)     => (h₂, .exn e)
        | (h₂, .hole l)    => (h₂, .hole l)
        | (h₂, .outOfFuel) => (h₂, .outOfFuel)
      | (h₁, .val _) => (h₁, .hole s!"setField:{f}:non-object")
      | (h₁, .exn e) => (h₁, .exn e)
      | (h₁, .hole l) => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .setIndex _ _ _ =>
      -- Container mutation needs boxed containers, which Core does not have yet.
      (h, .hole "setIndex:immutable-containers")
  | n+1, h, ρ, .seq a b =>
      match execStmt ctx n h ρ a with
      | (h₁, .normal ρ') => execStmt ctx n h₁ ρ' b
      | (h₁, r)          => (h₁, r)
  | n+1, h, ρ, .ifte c t e =>
      match evalExpr ctx n h ρ c with
      | (h₁, .val v)     => if v.truthy then execStmt ctx n h₁ ρ t
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
          if v.truthy then
            match execStmt ctx n h₁ ρ body with
            | (h₂, .normal ρ') => execStmt ctx n h₂ ρ' (.loop c body)
            | (h₂, .cont ρ')   => execStmt ctx n h₂ ρ' (.loop c body)
            | (h₂, .brk ρ')    => (h₂, .normal ρ')
            | (h₂, r)          => (h₂, r)
          else (h₁, .normal ρ)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .forIn x e body =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v) =>
        match v.iterable with
        | some vs => execFor ctx n h₁ ρ x vs body
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

/-- Run a named entry point against argument values, with **no** module-level state.

Deliberately unchanged: it starts from the empty heap, so `Heap.get ctx.globals` finds
nothing and a free name falls through to the function table. This is the right entry point
for a self-contained function, and keeping it stable keeps the refinement layer's
theorems meaningful. Use `runMain` when module-level bindings matter. -/
def runFunc (p : Program) (fuel : Nat) (name : String) (args : List Val) : EResult :=
  let ctx : Ctx := { dialect := p.dialect, table := p.table,
                     builtinBases := p.builtinBases }
  match ctx.resolve name with
  | none    => .hole s!"entry:{name}"
  | some fn => (applyFunc ctx fuel [] fn none args).2

/-- Run the module initializers and return the resulting heap plus the globals address.

Exposed separately from `runMain` so that a harness which builds its own heap (e.g. the
differential oracle, which materialises receiver objects) can start from an initialised
globals frame instead of the empty heap. Fresh objects must be allocated at indices from
`heap.length` onward. -/
def initGlobals (p : Program) (fuel : Nat) (inits : List Func) : Heap × Ref :=
  let (h₀, g) := Heap.alloc ([] : Heap) { cls := "<globals>", fields := [] }
  let ctx : Ctx := { dialect := p.dialect, table := p.table, globals := g,
                     builtinBases := p.builtinBases }
  let rec go : Nat → Heap → List Func → Heap
    | 0,   h, _       => h
    | _+1, h, []      => h
    | n+1, h, f :: fs => go n (applyFunc ctx fuel h f none []).1 fs
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
                     builtinBases := p.builtinBases }
  let rec runInits : Nat → Heap → List Func → Heap × Option String
    | 0,   h, _       => (h, some "initializers:outOfFuel")
    | _+1, h, []      => (h, none)
    | n+1, h, f :: fs =>
        match applyFunc ctx fuel h f none [] with
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
    | some fn => (applyFunc ctx fuel h₁ fn none args).2

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

end Autoform.Core
