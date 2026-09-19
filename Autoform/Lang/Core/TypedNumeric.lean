import Autoform.Lang.Core.Numeric

/-!
Numeric operators whose language and promoted operand type survive CPG export.
The encoding is `num:<c|java|go|js>:<i|u><width>:<operator>`. Untyped legacy
operators keep their existing semantics. Unknown encodings remain holes.
-/
namespace Autoform.Core.TypedNumeric

def intType : String → Option IntType
  | "i8" => some (.signed .w8) | "u8" => some (.unsigned .w8)
  | "i16" => some (.signed .w16) | "u16" => some (.unsigned .w16)
  | "i32" => some (.signed .w32) | "u32" => some (.unsigned .w32)
  | "i64" => some (.signed .w64) | "u64" => some (.unsigned .w64)
  | _ => none

/-- A structural parser keeps concrete tagged operations cheap to reduce in the
kernel. String.splitOn's byte-position termination proof is costly here. -/
def fields : List Char → List Char → List (List Char)
  | [], part => [part.reverse]
  | ':' :: rest, part => part.reverse :: fields rest []
  | c :: rest, part => fields rest (c :: part)

def parse (code : String) : Option (String × NumConfig × String) := do
  let [['n', 'u', 'm'], familyChars, ty, op] := fields code.toList [] | none
  let family ← match familyChars with
    | ['c'] => some "c"
    | ['j', 'a', 'v', 'a'] => some "java"
    | ['g', 'o'] => some "go"
    | ['j', 's'] => some "js"
    | _ => none
  let t ← intType (String.ofList ty)
  let cfg ← match family with
    | "c" => some { NumConfig.c32 with type := t }
    | "java" => some { NumConfig.java32 with type := t }
    | "go" => some { NumConfig.go64 with type := t }
    | "js" => if t == .signed .w32 then some NumConfig.java32 else none
    | _ => none
  pure (family, cfg, String.ofList op)

def result (family : String) : NumResult → EResult
  | .ok n => .val (.int n)
  | .ub why => .hole s!"ub:{why}"
  | .trap why => .exn (.str why)
  | .divZero => match family with
    | "c" => .hole "ub:division by zero"
    | "java" => .exn (.str "ArithmeticException")
    | "go" => .exn (.str "panic:integer divide by zero")
    | _ => .hole "numeric:division-by-zero"

/-- ECMAScript ToInt32 for numeric/boolean/unit inputs. Strings and objects need
ToNumber/ToPrimitive and stay holes. Round stored integer Numbers to binary64
before truncation; treating a mathematical integer as a Number past 2^53 is wrong. -/
def jsInt (v : Val) : Option Int :=
  let ofFloat (f : Fl) := match FConfig.cDouble.toInt f with
    | .ok n => IntType.wrap (.signed .w32) n
    | .error _ => 0  -- NaN and infinities become zero in ToInt32.
  match v with
  | .int n =>
    -- Every integer in this range is exactly representable as binary64. In
    -- particular, avoid constructing subnormal exponents merely to coerce zero.
    if n.natAbs ≤ 9007199254740992 then some (IntType.wrap (.signed .w32) n)
    else match FConfig.cDouble.ofInt n with
      | .ok f => some (ofFloat f)
      | _ => none
  | .float f => some (ofFloat f)
  | .bool b => some (if b then 1 else 0)
  | .unit => some 0
  | _ => none

def operand (family : String) (v : Val) : Option Int :=
  if family == "js" then jsInt v else
  match v with
  | .int n => some n
  | .bool b => if family == "c" then some (if b then 1 else 0) else none
  | _ => none

/-- Go saturates wide shift counts instead of masking them as Java does. -/
def shift (family : String) (cfg : NumConfig) (op : String) (a b : Int) : NumResult :=
  if family == "go" && b < 0 then .trap "panic:negative shift amount"
  else if family == "go" && b ≥ (cfg.type.bits : Int) then
    .ok (if op == ">>" && a < 0 then -1 else 0)
  else if family == "c" && op == "<<" && cfg.type.isSigned && a < 0 then
    .ub "left shift of a negative value"
  else if op == "<<" then cfg.shl a b
  else if op == ">>>" then
    if family == "js" then
      ({ cfg with type := .unsigned .w32, negRightShift := .logical } : NumConfig).shr
        (IntType.wrap (.unsigned .w32) a) b
    else ({ cfg with negRightShift := .logical } : NumConfig).shr a b
  else cfg.shr a b

def binary (code : String) (left right : Val) : EResult :=
  match parse code with
  | none => .hole s!"binop:{code}"
  | some (family, cfg, op) =>
    match operand family left, operand family right with
    | some x, some y =>
      let a := cfg.type.wrap x
      let b := cfg.type.wrap y
      if family == "js" && !(["&", "|", "^", "<<", ">>", ">>>"].contains op) then
        .hole s!"numeric:unsupported-js-op:{op}"
      else match op with
      | "+" => result family (cfg.add a b)
      | "-" => result family (cfg.sub a b)
      | "*" => result family (cfg.mul a b)
      | "/" => result family (cfg.div a b)
      | "%" => result family (cfg.mod a b)
      | "&" => result family (cfg.band a b)
      | "|" => result family (cfg.bor a b)
      | "^" => result family (cfg.bxor a b)
      | "<<" | ">>" | ">>>" => result family (shift family cfg op a y)
      | "<" => .val (.bool (a < b))
      | "<=" => .val (.bool (a ≤ b))
      | ">" => .val (.bool (a > b))
      | ">=" => .val (.bool (a ≥ b))
      | "==" => .val (.bool (a == b))
      | "!=" => .val (.bool (a != b))
      | _ => .hole s!"binop:{code}"
    | _, _ => .hole s!"numeric:operand:{code}"

def unary (code : String) (value : Val) : EResult :=
  match parse code with
  | none => .hole s!"unop:{code}"
  | some (family, cfg, op) =>
    match operand family value with
    | none => .hole s!"numeric:operand:{code}"
    | some n =>
      let a := cfg.type.wrap n
      match op with
      | "~" => result family (cfg.bnot a)
      | "-" => if family == "js" then .hole "numeric:unsupported-js-op:-"
               else result family (cfg.neg a)
      | _ => .hole s!"unop:{code}"

end Autoform.Core.TypedNumeric
