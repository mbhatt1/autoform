import Autoform.Lang.PCode.Semantics

namespace Autoform.PCode

/-- Width belongs to the operand, not to a source-language default. -/
example : unsigned 1 256 = 0 := by rfl
example : unsigned 8 (-1) = 18446744073709551615 := by rfl
example : signed 1 255 = -1 := by rfl
example : evalBinary "INT_SDIV" 249 3 1 1 1 = .ok 254 := by rfl
example : evalBinary "INT_SREM" 249 3 1 1 1 = .ok 255 := by rfl
example : evalBinary "INT_SRIGHT" 128 100 1 8 1 = .ok 255 := by rfl
example : evalBinary "INT_RIGHT" 128 100 1 8 1 = .ok 0 := by rfl
example : evalBinary "INT_LEFT" 1 1000000000 1 8 1 = .ok 0 := by rfl
example : evalBinary "INT_CARRY" 255 1 1 1 1 = .ok 1 := by rfl
example : evalBinary "INT_SCARRY" 127 1 1 1 1 = .ok 1 := by rfl
example : evalBinary "INT_SBORROW" 128 1 1 1 1 = .ok 1 := by rfl
example : evalBinary "SUBPIECE" 305419896 1 4 4 2 = .ok 1193046 := by rfl
example : evalBinary "PIECE" 18 52 1 1 2 = .ok 4660 := by rfl
example : evalUnary "LZCOUNT" 1 4 1 = .ok 31 := by rfl
example : evalUnary "POPCOUNT" 255 4 1 = .ok 8 := by rfl
example : evalUnary "FLOAT_SQRT" 0 8 8 = .error "unsupported-op:FLOAT_SQRT" := by rfl
example : evalBinary "INT_DIV" 1 0 8 8 8 = .error "division-by-zero" := by rfl

private def sample : Program := ⟨"test", false, "ram", [⟨4096, 4, []⟩]⟩

/-- A byte write updates an overlapping register view; uninitialized bytes stay unknown. -/
example : readBytes (writeBytes (writeBytes [] "register" 0 false 8 0x1122334455667788)
    "register" 0 false 1 0xFF) "register" 0 false 8 = .ok 0x11223344556677FF := by rfl
example : readBytes (writeBytes [] "ram" 0 true 4 0x12345678) "ram" 1 true 2 = .ok 0x3456 := by rfl
example : getByte [] "ram" 0 = .error "uninitialized:ram:0" := by rfl
example : write sample ⟨0, 0, []⟩ ⟨"ram", 4096, 1⟩ 0 = .error "self-modifying-code" := by rfl
example : writeOutput sample ⟨0, 0, []⟩ { code := "COPY", guardValue := some 0 }
    ⟨"register", 0, 1⟩ 1 = .error "dynamic-instruction-mode" := by rfl

/-- A missing destination and exhaustion are not successful execution. -/
example : run sample [] 1 ⟨100, 0, []⟩ = .hole "missing-instruction:100" ⟨100, 0, []⟩ := by rfl
example : run sample [] 0 ⟨4096, 0, []⟩ = .outOfFuel ⟨4096, 0, []⟩ := by rfl
example : run sample [4100] 1 ⟨4096, 0, []⟩ = .stopped ⟨4100, 0, []⟩ := by rfl

/-- Relative p-code branches use operation indexes and signed offsets. -/
private def loop : Instruction := ⟨0, 1, [{ code := "BRANCH", inputs := [⟨"const", 0, 4⟩] }]⟩
example : run ⟨"test", false, "ram", [loop]⟩ [] 10 ⟨0, 0, []⟩ =
    .outOfFuel ⟨0, 0, []⟩ := by rfl
example : branch sample ⟨0, 1, [{ code := "COPY" }, { code := "BRANCH" }]⟩ ⟨0, 1, []⟩
    ⟨"const", 4294967295, 4⟩ = .ok ⟨0, 0, []⟩ := by rfl

end Autoform.PCode
