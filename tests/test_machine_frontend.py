"""Real SLEIGH lifting, Lean execution, and independent native conformance."""
from __future__ import annotations

import ctypes
import json
import os
from pathlib import Path
import platform
import random
import shutil
import struct
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.binary_loader import load_image
from scripts.formalize_machine import coverage, lean_var, lift_image, render_assertions, render_model


def test_missing_optional_dependency_invalidates_previous_report(tmp_path, monkeypatch):
    from scripts.formalize_machine import main
    report = tmp_path / "report.json"
    report.write_text(json.dumps(dict(status="MODEL_TYPECHECKED", property_proved=True)))
    binary = tmp_path / "code.bin"
    binary.write_bytes(bytes.fromhex("c3"))
    monkeypatch.setitem(sys.modules, "pypcode", None)
    assert main([str(binary), "Missing", "--format", "raw", "--language", "x86:LE:64:default",
                 "--out", str(tmp_path)]) == 1
    failed = json.loads(report.read_text())
    assert failed["status"] == "FAILED" and not failed["property_proved"]


@pytest.fixture(scope="module")
def pcode():
    return pytest.importorskip("pypcode", reason="install requirements-machine.txt for machine frontend tests")


@pytest.fixture(scope="module")
def lean_env():
    # Keep credentials out of pytest's fixture/argument representations on failure.
    env = {k: os.environ[k] for k in ("PATH", "HOME", "LANG", "LC_ALL", "TMPDIR", "LEAN_NUM_THREADS") if k in os.environ}
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    if not shutil.which("lake", path=env["PATH"]):
        if os.environ.get("AUTOFORM_REQUIRE_LEAN"):
            pytest.fail("Lean is required by this test job")
        pytest.skip("Lean toolchain not installed")
    result = subprocess.run(["lake", "build", "Autoform.Lang.PCode.Properties"],
                            cwd=ROOT, env=env, text=True, capture_output=True, timeout=180)
    assert result.returncode == 0, result.stdout + result.stderr
    return env


def raw_doc(tmp_path, language, hexcode):
    path = tmp_path / "code.bin"
    path.write_bytes(bytes.fromhex(hexcode))
    return lift_image(load_image(path, "raw", language, base=0x1000))


def observe(tmp_path, env, doc, reg_a, reg_b, reg_out, cases, *, return_reg=None,
            stop=None, stack=None, prove_first=True):
    """Run the generated Lean model, not a Python implementation of p-code."""
    reg = lambda name: lean_var(doc["registers"][name])
    stop = stop if stop is not None else doc["instructions"][-1]["address"]
    seed = f"writeBytes s.memory {json.dumps(doc['codeSpace'])} 32768 program.bigEndian 8 {stop}" if stack else "s.memory"
    setup = f"let s := initialState {doc['instructions'][0]['address']}\n"
    setup += f"  let s := {{ s with memory := {seed} }}\n"
    if stack:
        setup += f"  let s ← write program s ({reg(stack)}) 32768\n"
    if return_reg:
        setup += f"  let s ← write program s ({reg(return_reg)}) {stop}\n"
    setup += f"  let s ← write program s ({reg(reg_a)}) a\n"
    setup += f"  write program s ({reg(reg_b)}) b\n"
    driver = render_model(doc, "Test") + f'''
open Autoform.PCode Autoform.Machine.Test
def seedState (a b : Nat) : Except String State := do
  {setup}
def observe (a b : Nat) : Except String Nat := do
  let s ← seedState a b
  match run program [{stop}] 1000 s with
  | .stopped final => read program final ({reg(reg_out)})
  | .hole why _ => throw why
  | .outOfFuel _ => throw "out-of-fuel"
'''
    if prove_first:
        a, b, expected = cases[0]
        driver += f"example : observe {a} {b} = .ok {expected} := by rfl\n"
    pairs = ", ".join(f"({a}, {b})" for a, b, _ in cases)
    driver += f'''
def main : IO Unit := do
  for (a, b) in ([{pairs}] : List (Nat × Nat)) do
    match observe a b with
    | .ok value => IO.println value
    | .error why => throw (IO.userError why)
'''
    path = tmp_path / "Execute.lean"
    path.write_text(driver)
    proc = subprocess.run(["lake", "env", "lean", "--run", str(path)], cwd=ROOT,
                          env=env, text=True, capture_output=True, timeout=180)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    actual = [int(line) for line in proc.stdout.splitlines() if line.isdecimal()]
    assert actual == [expected for _, _, expected in cases]


@pytest.mark.parametrize("language,code,a,b,out,width", [
    ("x86:LE:64:default", "488d0437c3", "RDI", "RSI", "RAX", 64),
    ("AARCH64:LE:64:v8A", "0000018bc0035fd6", "x0", "x1", "x0", 64),
    ("RISCV:LE:64:RV64GC", "3305b50067800000", "a0", "a1", "a0", 64),
    ("MIPS:BE:32:default", "0085102103e0000800000000", "a0", "a1", "v0", 32),
])
def test_arithmetic_across_isas(tmp_path, pcode, lean_env, language, code, a, b, out, width):
    doc = raw_doc(tmp_path, language, code)
    assert not coverage(doc)["unsupported_operations"]
    assert not doc["decodeErrors"]
    pairs = [(3, 4), (2**width - 1, 1), (2**(width-1), 2**(width-1)), (12345, 67890)]
    stop = doc["instructions"][1]["address"]  # before the return (and its delay slot)
    observe(tmp_path, lean_env, doc, a, b, out,
            [(x, y, (x+y) % 2**width) for x, y in pairs], stop=stop)


def test_unknown_memory_is_a_hole(tmp_path, pcode, lean_env):
    doc = raw_doc(tmp_path, "x86:LE:64:default", "488b07c3")
    code = render_model(doc, "Read") + '''
open Autoform.PCode Autoform.Machine.Read
example : run program [] 10 (initialState 4096) =
  .hole "uninitialized:register:56" (initialState 4096) := by rfl
'''
    path = tmp_path / "Unknown.lean"
    path.write_text(code)
    result = subprocess.run(["lake", "env", "lean", str(path)], env=lean_env,
                            cwd=ROOT, text=True, capture_output=True, timeout=120)
    assert result.returncode == 0, result.stdout + result.stderr


def test_unimplemented_instruction_is_counted(tmp_path, pcode):
    doc = raw_doc(tmp_path, "x86:LE:64:default", "0f05c3")  # syscall; ret
    report = coverage(doc)
    assert report["instructions_with_unmodelled_ops"] == 1
    assert report["unsupported_operations"]["CALLOTHER"] == 1


def test_truncated_instruction_and_budget_are_reported(tmp_path, pcode):
    path = tmp_path / "code.bin"
    path.write_bytes(bytes.fromhex("9048"))  # NOP then incomplete REX instruction
    image = load_image(path, "raw", "x86:LE:64:default", 4096)
    doc = lift_image(image)
    assert len(doc["instructions"]) == 1
    assert doc["decodeErrors"][0]["address"] == 4097
    path.write_bytes(b"\x90\x90")
    doc = lift_image(load_image(path, "raw", image.language), max_instructions=1)
    assert doc["decodeErrors"][0]["reason"] == "instruction-limit"


def test_raw_requires_explicit_format_and_language(tmp_path):
    path = tmp_path / "source.s"
    path.write_text("add x0, x0, x1\n")
    with pytest.raises(ValueError, match="unrecognized executable format"):
        load_image(path)
    with pytest.raises(ValueError, match="require --language"):
        load_image(path, "raw")


def test_deterministic_render(tmp_path, pcode):
    doc = raw_doc(tmp_path, "x86:LE:64:default", "488d0437c3")
    assert render_model(doc, "Sample") == render_model(json.loads(json.dumps(doc)), "Sample")
    with pytest.raises(ValueError, match="module must"):
        render_model(doc, "X\nend X")


def test_cli_reports_gaps_and_invalidates_old_success(tmp_path, pcode):
    source = tmp_path / "code.bin"
    source.write_bytes(bytes.fromhex("0f05c3"))
    out = tmp_path / "result"
    cmd = [sys.executable, str(ROOT / "scripts/formalize_machine.py"), str(source), "Test",
           "--format", "raw", "--language", "x86:LE:64:default", "--emit-only", "--out", str(out)]
    result = subprocess.run(cmd, text=True, capture_output=True, timeout=30)
    assert result.returncode == 3, result.stdout + result.stderr
    report = json.loads((out / "report.json").read_text())
    assert report["status"] == "UNCHECKED" and not report["property_proved"]
    assert report["unsupported_operations"] == {"CALLOTHER": 1}
    source.write_bytes(b"")
    result = subprocess.run(cmd, text=True, capture_output=True, timeout=30)
    assert result.returncode == 1
    assert json.loads((out / "report.json").read_text())["status"] == "FAILED"
    source.unlink()
    result = subprocess.run(cmd, text=True, capture_output=True, timeout=30)
    assert result.returncode == 1
    assert "not a file" in json.loads((out / "report.json").read_text())["error"]


@pytest.mark.parametrize("body", [
    "return ((a + b) ^ 0x12345678ULL) * 3;",
    "if (a & 1) return a / (b | 1); return a ^ b;",
    "for (unsigned i=0; i<(b & 15); ++i) a=(a ^ i)*3; return a;",
    "return ((a+b<a)?1:0) | ((a-b>a)?2:0) | (((long long)a<(long long)b)?4:0);",
    "return ((long long)a >> (b & 63)) ^ (a << (b & 63)) ^ (a >> ((b ^ 7) & 63));",
])
def test_native_compiler_output_matches_lean(tmp_path, pcode, lean_env, body):
    """Independent oracle: real native execution of the same compiler's bytes."""
    clang = shutil.which("clang")
    if not clang or platform.machine().lower() not in ("arm64", "aarch64", "x86_64", "amd64"):
        pytest.skip("native clang oracle requires AArch64 or x86-64")
    source = tmp_path / "arithmetic.c"
    source.write_text("unsigned long long sample(unsigned long long a, unsigned long long b) { " + body + " }\n")
    obj, library = tmp_path / "arithmetic.o", tmp_path / "arithmetic.so"
    arch_flags = ["-arch", platform.machine()] if sys.platform == "darwin" else []
    for args in (["-c", "-o", str(obj)],
                 ["-dynamiclib" if sys.platform == "darwin" else "-shared", "-o", str(library)]):
        proc = subprocess.run([clang, *arch_flags, "-O2", "-fPIC", "-fno-stack-protector",
                               "-fno-asynchronous-unwind-tables", "-fno-unwind-tables", str(source), *args],
                              text=True, capture_output=True, timeout=60)
        assert proc.returncode == 0, proc.stderr
    image = load_image(obj)
    assert not any("relocations" in gap for gap in image.gaps)
    doc = lift_image(image)
    assert not doc["decodeErrors"] and not coverage(doc)["unsupported_operations"]
    native = ctypes.CDLL(str(library)).sample
    native.argtypes, native.restype = [ctypes.c_uint64, ctypes.c_uint64], ctypes.c_uint64
    rng = random.Random(472)
    pairs = [(0, 0), (2**64-1, 1), (2**63, 2**63)] + [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(64)]
    cases = [(a, b, native(a, b)) for a, b in pairs]
    if image.language.startswith("AARCH64"):
        observe(tmp_path, lean_env, doc, "x0", "x1", "x0", cases, stop=0xDEAD, return_reg="x30")
    else:
        observe(tmp_path, lean_env, doc, "RDI", "RSI", "RAX", cases, stop=0xDEAD, stack="RSP")


def test_machine_store_load_and_register_aliases(tmp_path, pcode, lean_env):
    doc = raw_doc(tmp_path, "x86:LE:64:default", "488937488b07c3")
    observe(tmp_path, lean_env, doc, "RDI", "RSI", "RAX",
            [(0x8000, 0x123456789ABCDEF0, 0x123456789ABCDEF0)])
    doc = raw_doc(tmp_path, "x86:LE:64:default", "89f84088f0c3")  # eax <- edi; al <- sil
    observe(tmp_path, lean_env, doc, "RDI", "RSI", "RAX",
            [(0x123456789ABCDEF0, 0x77, 0x9ABCDE77)])


def test_mips_return_executes_delay_slot(tmp_path, pcode, lean_env):
    doc = raw_doc(tmp_path, "MIPS:BE:32:default", "0085102103e0000824420001")
    assert doc["instructions"][1]["length"] == 8
    observe(tmp_path, lean_env, doc, "a0", "a1", "v0", [(3, 4, 8), (0xFFFFFFFF, 0, 0)],
            return_reg="ra", stop=0xDEAC)


def test_pe_loader_uses_virtual_addresses(tmp_path, pcode):
    # A minimal PE32+ with a real x86-64 text section, independent of host OS.
    data = bytearray(1024)
    data[:2] = b"MZ"
    struct.pack_into("<I", data, 0x3C, 0x80)
    data[0x80:0x84] = b"PE\0\0"
    struct.pack_into("<HHIIIHH", data, 0x84, 0x8664, 1, 0, 0, 0, 240, 0x22)
    opt = 0x98
    struct.pack_into("<H", data, opt, 0x20B)
    struct.pack_into("<II", data, opt + 16, 0x1000, 0x1000)
    struct.pack_into("<Q", data, opt + 24, 0x140000000)
    struct.pack_into("<II", data, opt + 32, 0x1000, 0x200)
    struct.pack_into("<II", data, opt + 56, 0x2000, 0x200)
    struct.pack_into("<I", data, opt + 108, 16)
    struct.pack_into("<8sIIIIIIHHI", data, opt + 240,
                     b".text\0\0\0", 5, 0x1000, 0x200, 0x200, 0, 0, 0, 0, 0x60000020)
    data[512:517] = bytes.fromhex("488d0437c3")
    path = tmp_path / "sample.exe"
    path.write_bytes(data)
    image = load_image(path)
    assert image.entry == image.code[0].address == 0x140001000
    assert len(image.code[0].data) == 5
    doc = lift_image(image)
    assert len(doc["instructions"]) == 2 and not doc["decodeErrors"]
    path.write_bytes(data[:516])
    with pytest.raises(ValueError, match="truncated PE section"):
        load_image(path)


def test_assembly_cli_proves_observation_and_rejects_false_one(tmp_path, pcode, lean_env):
    if not shutil.which("clang"):
        pytest.skip("clang assembler absent")
    out = tmp_path / "proof"
    cmd = [sys.executable, str(ROOT / "scripts/formalize_machine.py"),
           str(ROOT / "examples/machine/add_aarch64.s"), "Add",
           "--assemble", "aarch64-unknown-linux-gnu", "--entry", "0",
           "--register", "x0=3", "--register", "x1=4", "--stop", "4",
           "--out", str(out), "--expect"]
    proc = subprocess.run(cmd + ["x0=7"], cwd=ROOT, env=lean_env, text=True, capture_output=True, timeout=120)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads((out / "report.json").read_text())
    assert report["assertions"]["proved"] and not report["source_refinement_proved"]
    proc = subprocess.run(cmd + ["x0=8"], cwd=ROOT, env=lean_env, text=True, capture_output=True, timeout=120)
    assert proc.returncode == 1
    report = json.loads((out / "report.json").read_text())
    assert report["status"] == "FAILED" and not report["assertions"]["proved"]


def test_relocations_block_execution(tmp_path, pcode):
    clang = shutil.which("clang")
    if not clang:
        pytest.skip("clang assembler absent")
    source, obj = tmp_path / "external.s", tmp_path / "external.o"
    source.write_text(".text\n.global sample\nsample:\n  bl external\n  ret\n")
    result = subprocess.run([clang, "-target", "aarch64-unknown-linux-gnu", "-c", str(source), "-o", str(obj)],
                            text=True, capture_output=True, timeout=60)
    assert result.returncode == 0, result.stderr
    doc = lift_image(load_image(obj))
    assert coverage(doc)["unsupported_operations"]["loader:unapplied-relocations"] == 2
    assert doc["memory"] == []


@pytest.mark.parametrize("target,data_section", [
    ("aarch64-unknown-linux-gnu", ".data"),
    ("arm64-apple-macos11", ".section __DATA,__data"),
])
def test_data_relocations_withhold_memory_without_blocking_independent_code(
        tmp_path, pcode, lean_env, target, data_section):
    clang = shutil.which("clang")
    if not clang:
        pytest.skip("clang assembler absent")
    source, obj = tmp_path / "data_fixup.s", tmp_path / "data_fixup.o"
    source.write_text(".text\nsample:\n  add x0, x0, x1\n  ret\n" +
                      data_section + "\n.quad external\n")
    result = subprocess.run([clang, "-target", target, "-c", str(source), "-o", str(obj)],
                            text=True, capture_output=True, timeout=60)
    assert result.returncode == 0, result.stderr
    doc = lift_image(load_image(obj))
    assert any(gap.startswith("unapplied-data-relocations:") for gap in doc["loaderGaps"])
    assert not coverage(doc)["unsupported_operations"]
    assert doc["memory"] == []
    observe(tmp_path, lean_env, doc, "x0", "x1", "x0", [(3, 4, 7)])


def test_multiple_models_and_proofs_can_coexist(tmp_path, pcode, lean_env):
    doc = raw_doc(tmp_path, "x86:LE:64:default", "488d0437c3")
    pieces = []
    for module in ("First", "Second"):
        model = render_model(doc, module)
        if pieces:
            model = model.replace("import Autoform.Lang.PCode.Semantics\n", "", 1)
        pieces += [model, render_assertions(doc, module, {"RDI": 3, "RSI": 4}, {},
                                          [4100], {"RAX": 7}, 100)]
    path = tmp_path / "Together.lean"
    path.write_text("\n".join(pieces))
    result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, env=lean_env,
                            capture_output=True, text=True, timeout=120)
    assert result.returncode == 0, result.stdout + result.stderr
