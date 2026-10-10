import Autoform.Lang.PCode.Syntax

/-!
# Total, fuel-indexed execution of integer raw p-code

See Ghidra's P-Code Operation Reference. Calls and returns are branches: the
surrounding raw p-code implements the architecture's stack/link-register effects.
No syscall, floating-point operation, unknown byte, or external destination is
silently executed. There is no assumed ABI and no implicit return-value register.
-/

namespace Autoform.PCode

def modulus (size : Nat) : Nat := 2 ^ (8 * size)

def unsigned (size : Nat) (value : Int) : Nat :=
  (value % (modulus size : Int)).toNat

def signed (size value : Nat) : Int :=
  let v := value % modulus size
  if v < modulus size / 2 then (v : Int) else (v : Int) - modulus size

def getByte (m : Memory) (space : String) (address : Nat) : Except String Nat :=
  match m.find? (fun cell => cell.1 == (space, address)) with
  | some cell => .ok (cell.2 % 256)
  | none => .error s!"uninitialized:{space}:{address}"

def readBytes (m : Memory) (space : String) (address : Nat) (big : Bool) :
    Nat → Except String Nat
  | 0 => .ok 0
  | n + 1 => do
    let b ← getByte m space address
    let rest ← readBytes m space (address + 1) big n
    pure (if big then b * 256 ^ n + rest else b + 256 * rest)

def putByte (m : Memory) (space : String) (address value : Nat) : Memory :=
  ((space, address), value % 256) :: m.filter (fun c => c.1 != (space, address))

def writeBytes (m : Memory) (space : String) (address : Nat) (big : Bool) :
    Nat → Nat → Memory
  | 0, _ => m
  | n + 1, value =>
    let b := if big then value / 256 ^ n else value % 256
    let rest := if big then value else value / 256
    writeBytes (putByte m space address b) space (address + 1) big n rest

def read (p : Program) (s : State) (v : Varnode) : Except String Nat :=
  if v.size == 0 then .error "zero-sized-varnode"
  else if v.space == "const" then .ok (v.offset % modulus v.size)
  else readBytes s.memory v.space v.offset p.bigEndian v.size

/-- Changing translated code would require lifting the new bytes, not executing the
old instructions. Detect this at the write, including writes through STORE. -/
def write (p : Program) (s : State) (v : Varnode) (value : Nat) : Except String State :=
  if v.size == 0 || v.space == "const" then .error "invalid-output-varnode"
  else if v.space == p.codeSpace && p.instructions.any (fun i =>
      v.offset < i.address + i.length && i.address < v.offset + v.size) then
    .error "self-modifying-code"
  else .ok { s with memory := writeBytes s.memory v.space v.offset p.bigEndian v.size value }

def bit (b : Bool) : Nat := if b then 1 else 0

def signedOverflow (size : Nat) (value : Int) : Bool :=
  let half : Int := modulus size / 2
  value < -half || value ≥ half

/-- Integer operations use the operand's width, and the write truncates to the
output width. Shifts saturate at the width rather than allocating huge integers. -/
def evalUnary (code : String) (a : Nat) (size outSize : Nat) : Except String Nat :=
  match code with
  | "COPY" | "INT_ZEXT" => .ok a
  | "INT_SEXT" => .ok (unsigned outSize (signed size a))
  | "INT_2COMP" => .ok (unsigned outSize (-(a : Int)))
  | "INT_NEGATE" => .ok (modulus size - 1 - a)
  | "BOOL_NEGATE" => .ok (bit (a == 0))
  | "POPCOUNT" => .ok ((List.range (8 * size)).foldl
      (fun count i => count + (a / 2 ^ i) % 2) 0)
  | "LZCOUNT" => .ok ((List.range (8 * size)).takeWhile
      (fun i => (a / 2 ^ (8 * size - 1 - i)) % 2 == 0)).length
  | _ => .error s!"unsupported-op:{code}"

def evalBinary (code : String) (a b size sizeB outSize : Nat) : Except String Nat :=
  let sa := signed size a
  let sb := signed sizeB b
  match code with
  | "INT_ADD" => .ok (a + b)
  | "INT_SUB" => .ok (unsigned outSize ((a : Int) - b))
  | "INT_MULT" => .ok (a * b)
  | "INT_DIV" => if b == 0 then .error "division-by-zero" else .ok (a / b)
  | "INT_REM" => if b == 0 then .error "division-by-zero" else .ok (a % b)
  | "INT_SDIV" => if b == 0 then .error "division-by-zero"
      else .ok (unsigned outSize (Int.tdiv sa sb))
  | "INT_SREM" => if b == 0 then .error "division-by-zero"
      else .ok (unsigned outSize (Int.tmod sa sb))
  | "INT_AND" => .ok (Nat.land a b)
  | "INT_OR" => .ok (Nat.lor a b)
  | "INT_XOR" => .ok (Nat.xor a b)
  | "INT_LEFT" => .ok (if b ≥ 8 * size then 0 else a * 2 ^ b)
  | "INT_RIGHT" => .ok (if b ≥ 8 * size then 0 else a / 2 ^ b)
  | "INT_SRIGHT" => .ok (unsigned outSize (sa / (2 ^ min b (8 * size) : Nat)))
  | "INT_EQUAL" => .ok (bit (a == b))
  | "INT_NOTEQUAL" => .ok (bit (a != b))
  | "INT_LESS" => .ok (bit (a < b))
  | "INT_LESSEQUAL" => .ok (bit (a ≤ b))
  | "INT_SLESS" => .ok (bit (sa < sb))
  | "INT_SLESSEQUAL" => .ok (bit (sa ≤ sb))
  | "INT_CARRY" => .ok (bit (a + b ≥ modulus size))
  | "INT_SCARRY" => .ok (bit (signedOverflow size (sa + sb)))
  | "INT_SBORROW" => .ok (bit (signedOverflow size (sa - sb)))
  | "BOOL_AND" => .ok (bit (a != 0 && b != 0))
  | "BOOL_OR" => .ok (bit (a != 0 || b != 0))
  | "BOOL_XOR" => .ok (bit ((a != 0) != (b != 0)))
  | "PIECE" => .ok (a * modulus sizeB + b)
  | "SUBPIECE" => .ok (if b ≥ size then 0 else a / 256 ^ b)
  | _ => .error s!"unsupported-op:{code}"

def jump (s : State) (address : Nat) : State :=
  { s with pc := address, micro := 0,
           memory := s.memory.filter (fun c => c.1.1 != "unique") }

def advance (i : Instruction) (s : State) : State :=
  if s.micro + 1 < i.ops.length then { s with micro := s.micro + 1 }
  else jump s (i.address + i.length)

def branch (p : Program) (i : Instruction) (s : State) (v : Varnode) :
    Except String State :=
  if v.space == "const" then
    let target := (s.micro : Int) + signed v.size v.offset
    if target < 0 || target > (i.ops.length : Int) then .error "invalid-pcode-branch"
    else if target == (i.ops.length : Int) then .ok (jump s (i.address + i.length))
    else .ok { s with micro := target.toNat }
  else if v.space == p.codeSpace then .ok (jump s v.offset)
  else .error s!"branch-space:{v.space}"

def writeOutput (p : Program) (s : State) (op : Op) (out : Varnode) (value : Nat) :
    Except String State :=
  if op.guardValue.any (· != value % modulus out.size) then
    .error "dynamic-instruction-mode"
  else write p s out value

def execOp (p : Program) (i : Instruction) (s : State) (op : Op) :
    Except String State := do
  match op.code, op.output, op.inputs with
  | "BRANCH", none, [dst] | "CALL", none, [dst] => branch p i s dst
  | "CBRANCH", none, [dst, cond] => do
    let c ← read p s cond
    if c != 0 then branch p i s dst else pure (advance i s)
  | "BRANCHIND", none, [dst] | "CALLIND", none, [dst] | "RETURN", none, [dst] => do
    let address ← read p s dst
    pure (jump s address)
  | "LOAD", some out, [ptr] => do
    let address ← read p s ptr
    if op.wordSize == 0 then throw "invalid-address-unit"
    if address * op.wordSize + out.size > modulus ptr.size * op.wordSize then
      throw "address-space-wrap"
    let value ← readBytes s.memory op.space (address * op.wordSize) p.bigEndian out.size
    let next ← writeOutput p s op out value
    pure (advance i next)
  | "STORE", none, [ptr, input] => do
    let address ← read p s ptr
    let value ← read p s input
    if op.wordSize == 0 then throw "invalid-address-unit"
    if address * op.wordSize + input.size > modulus ptr.size * op.wordSize then
      throw "address-space-wrap"
    let next ← write p s ⟨op.space, address * op.wordSize, input.size⟩ value
    pure (advance i next)
  | _, some out, [input] => do
    let a ← read p s input
    let value ← evalUnary op.code a input.size out.size
    let next ← writeOutput p s op out value
    pure (advance i next)
  | _, some out, [left, right] => do
    let a ← read p s left
    let b ← read p s right
    let value ← evalBinary op.code a b left.size right.size out.size
    let next ← writeOutput p s op out value
    pure (advance i next)
  | _, _, _ => throw s!"unsupported-op:{op.code}"

def step (p : Program) (s : State) : Except String State := do
  let some i := p.instructions.find? (·.address == s.pc)
    | throw s!"missing-instruction:{s.pc}"
  match i.ops[s.micro]? with
  | some op => execOp p i s op
  | none => if s.micro == 0 && i.ops.isEmpty then pure (jump s (i.address + i.length))
            else throw "invalid-micro-pc"

/-- One unit of fuel per raw operation (or NOP), including intra-instruction loops.
An observation point is caller-supplied; falling out of translated code is a hole. -/
def run (p : Program) (stops : List Nat) : Nat → State → Outcome
  | 0, s => if s.micro == 0 && stops.contains s.pc then .stopped s else .outOfFuel s
  | n + 1, s =>
    if s.micro == 0 && stops.contains s.pc then .stopped s
    else match step p s with
      | .error reason => .hole reason s
      | .ok next => run p stops n next

/-- Reaching an observation point is stable when the fuel budget increases. -/
theorem run_stopped_mono (p : Program) (stops : List Nat) (n extra : Nat)
    (s final : State) (h : run p stops n s = .stopped final) :
    run p stops (n + extra) s = .stopped final := by
  induction n generalizing s with
  | zero =>
    simp only [run] at h
    split at h
    next hs => cases extra <;> simpa only [Nat.zero_add, run, hs, if_true] using h
    next => contradiction
  | succ n ih =>
    simp only [run] at h
    split at h
    next hs => simpa only [Nat.succ_add, run, hs, if_true] using h
    next hs =>
      cases hstep : step p s with
      | error reason => simp [hstep] at h
      | ok next =>
        simp only [hstep] at h
        simpa only [Nat.succ_add, run, hs, if_false, hstep] using ih next h

end Autoform.PCode
