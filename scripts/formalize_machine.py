#!/usr/bin/env python3
"""Machine code -> SLEIGH raw p-code -> executable Lean model + coverage report.

This formalizes the supplied machine code, independent of its source language.
It does not prove the compiler/lifter correct, infer a specification, or supply an OS.
Run --list-languages for the locally installed processor definitions.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from cartographer.render_lean import lean_str
from scripts.binary_loader import load_image

UNARY = {"COPY", "INT_ZEXT", "INT_SEXT", "INT_2COMP", "INT_NEGATE", "BOOL_NEGATE",
         "POPCOUNT", "LZCOUNT"}
BINARY = {"INT_ADD", "INT_SUB", "INT_MULT", "INT_DIV", "INT_REM", "INT_SDIV", "INT_SREM",
          "INT_AND", "INT_OR", "INT_XOR", "INT_LEFT", "INT_RIGHT", "INT_SRIGHT",
          "INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_LESSEQUAL", "INT_SLESS",
          "INT_SLESSEQUAL", "INT_CARRY", "INT_SCARRY", "INT_SBORROW", "BOOL_AND",
          "BOOL_OR", "BOOL_XOR", "PIECE", "SUBPIECE"}
CONTROL = {"BRANCH", "CBRANCH", "BRANCHIND", "CALL", "CALLIND", "RETURN", "LOAD", "STORE"}
SUPPORTED = UNARY | BINARY | CONTROL
# These processor families have byte-addressed RAM. Others can lift integer-only
# code too, but memory operations require an explicit space unit from the caller.
BYTE_ADDRESSED = {"x86", "AARCH64", "ARM", "RISCV", "MIPS", "PowerPC", "Sparc", "68000"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def varnode(v) -> dict:
    return {"space": v.space.name, "offset": int(v.offset), "size": int(v.size)}


def lift_image(image, *, max_instructions=100000, space_units=None, context=None) -> dict:
    import pypcode

    ctx = pypcode.Context(image.language)
    for key, value in sorted((context or {}).items()):
        ctx.setVariableDefault(key, value)
    space_units = dict(space_units or {})
    if ctx.language.ldef.get("processor") in BYTE_ADDRESSED:
        space_units.setdefault("ram", 1)
    instructions, errors, histogram = [], [], collections.Counter()
    relocations = any(g.startswith("unapplied-relocations:") for g in image.gaps)
    count = 0
    for region in sorted(image.code, key=lambda r: (r.address, r.name)):
        offset = 0
        while offset < len(region.data):
            address = region.address + offset
            if count >= max_instructions:
                errors.append({"address": address, "bytes": len(region.data) - offset,
                               "reason": "instruction-limit", "region": region.name})
                break
            try:
                dis = ctx.disassemble(region.data, base_address=address, offset=offset,
                                      max_instructions=1).instructions[0]
                if dis.length <= 0 or offset + dis.length > len(region.data):
                    raise ValueError("invalid instruction length")
                tx = ctx.translate(region.data, base_address=address, offset=offset,
                                   max_instructions=1)
                markers = [op for op in tx.ops if op.opcode.name == "IMARK"]
                if len(markers) != 1 or not markers[0].inputs:
                    raise ValueError("translation is not one complete instruction group")
                marks = markers[0].inputs
                if marks[0].offset != address:
                    raise ValueError("instruction marker address disagrees with decoder")
                end = max(v.offset + v.size for v in marks)
                if end > region.address + len(region.data):
                    raise ValueError("truncated delay slot")
                ops = []
                if relocations:
                    # Pre-link operand bytes cannot be interpreted as final addresses.
                    # Until relocations are applied, stop before any instruction effect.
                    ops.append({"code": "loader:unapplied-relocations", "output": None, "inputs": []})
                    histogram["loader:unapplied-relocations"] += 1
                for op in tx.ops:
                    code = op.opcode.name
                    if code == "IMARK":
                        continue
                    inputs = list(op.inputs)
                    record = {"code": code, "output": varnode(op.output) if op.output else None,
                              "inputs": [varnode(v) for v in inputs]}
                    if op.output:
                        register = ctx.getRegisterName(op.output.space, op.output.offset, op.output.size)
                        if register == "ISAModeSwitch":
                            # MIPS indirect branches can request a compressed ISA by
                            # setting the low target bit. Do not execute the target's
                            # default-mode disassembly after such a switch.
                            record["guardValue"] = 0
                        elif register == "TMode":
                            record["guardValue"] = (context or {}).get("TMode", 0)
                    if code in {"LOAD", "STORE"}:
                        space = inputs[0].getSpaceFromConst().name
                        record.update(space=space, wordSize=space_units.get(space, 0),
                                      inputs=[varnode(v) for v in inputs[1:]])
                        if not record["wordSize"]:
                            record["code"] = f"unmodelled-address-unit:{space}:{code}"
                    # Delayed/context-sensitive instruction modes are preserved in
                    # metadata. The CLI never guesses Thumb or another alternate mode.
                    histogram[record["code"]] += 1
                    ops.append(record)
                instructions.append({"address": address, "length": end - address,
                                     "bytes": region.data[offset:offset + dis.length].hex(),
                                     "assembly": f"{dis.mnem} {dis.body}".strip(), "ops": ops,
                                     "space": marks[0].space.name})
                count += 1
                # A delay slot can also be a branch target. Decode it independently,
                # while keeping it in the preceding instruction's p-code as SLEIGH does.
                offset += dis.length
            except (pypcode.BadDataError, pypcode.UnimplError, pypcode.LowlevelError,
                    ValueError, IndexError) as exc:
                # Do not resynchronize at guessed instruction boundaries.
                errors.append({"address": address, "bytes": len(region.data) - offset,
                               "reason": str(exc) or type(exc).__name__, "region": region.name})
                break
    if not instructions:
        raise ValueError(f"no instructions lifted: {errors}")
    spaces = {i["space"] for i in instructions}
    if len(spaces) != 1:
        raise ValueError(f"multiple executable address spaces are not yet modelled: {sorted(spaces)}")
    code_space = next(iter(spaces))
    # Indirect control flow in word-addressed code needs a separate PC conversion.
    # Preserve it as a hole until that conversion is modelled.
    if space_units.get(code_space) != 1:
        for instruction in instructions:
            for op in instruction["ops"]:
                if op["code"] in {"BRANCHIND", "CALLIND", "RETURN"}:
                    histogram[op["code"]] -= 1
                    op["code"] = "unmodelled-code-address-unit:" + op["code"]
                    histogram[op["code"]] += 1
    return {
        "schema": "autoform.raw-pcode.v1", "language": image.language,
        "bigEndian": ctx.language.ldef.get("endian") == "big", "codeSpace": code_space,
        "entry": image.entry, "context": context or {}, "spaceUnits": space_units,
        "instructions": instructions, "decodeErrors": errors, "loaderGaps": image.gaps,
        "operations": dict(sorted((k, v) for k, v in histogram.items() if v)),
        "registers": {name: varnode(v) for name, v in sorted(ctx.registers.items())},
        # Imported/fixed-up pointers are unknown, not the placeholder bytes in a file.
        # Withhold the initial image when runtime loading is needed; the caller must
        # explicitly supply a relocated memory image to execute loads from it.
        "memory": [] if any("relocations" in g or "loader" in g or "imports" in g for g in image.gaps)
                  else [{"address": r.address, "hex": r.data.hex()} for r in image.data],
        "lifter": {"name": "pypcode", "version": pypcode.__version__,
                   "processor_sha256": sha(Path(ctx.language.slafile_path)),
                   "processor_spec_sha256": sha(Path(ctx.language.pspec_path))},
    }


def lean_var(v: dict) -> str:
    return f"⟨{lean_str(v['space'])}, {v['offset']}, {v['size']}⟩"


def render_model(doc: dict, module: str) -> str:
    if not re.fullmatch(r"[A-Z][A-Za-z0-9_]*", module):
        raise ValueError("module must start with an uppercase ASCII letter and contain only letters, digits, underscores")
    out = ["import Autoform.Lang.PCode.Semantics", "", "set_option maxRecDepth 16000",
           "set_option maxHeartbeats 0", "", f"namespace Autoform.Machine.{module}",
           "open Autoform.PCode", "",
           "-- Generated from raw machine-code p-code. Lifting faithfulness is unproved."]
    names = []
    for index, instruction in enumerate(doc["instructions"]):
        name = f"instruction_{index}"
        names.append(name)
        out.append(f"def {name} : Instruction :=")
        out.append(f"  {{ address := {instruction['address']}, length := {instruction['length']}, ops := [")
        rows = []
        for op in instruction["ops"]:
            output = f"some ({lean_var(op['output'])})" if op["output"] else "none"
            args = ", ".join(lean_var(v) for v in op["inputs"])
            guard = "none" if op.get("guardValue") is None else f"some {op['guardValue']}"
            rows.append(f"    {{ code := {lean_str(op['code'])}, output := {output}, inputs := [{args}], "
                        f"space := {lean_str(op.get('space', doc['codeSpace']))}, wordSize := {op.get('wordSize', 1)}, "
                        f"guardValue := {guard} }}")
        out.append(",\n".join(rows))
        out.append("  ] }")
    instruction_chunks = []
    for offset in range(0, len(names), 128):
        name = f"instructions_{offset // 128}"
        instruction_chunks.append(name)
        out.append(f"def {name} : List Instruction := [{', '.join(names[offset:offset + 128])}]")
    out += ["", "def program : Program :=", f"  {{ language := {lean_str(doc['language'])},",
            f"     bigEndian := {str(doc['bigEndian']).lower()}, codeSpace := {lean_str(doc['codeSpace'])},",
            f"     instructions := [{', '.join(instruction_chunks)}].flatten }}", ""]
    # SLEIGH exposes thousands of vector/subregister views on some processors.
    # Chunking bounds Lean's elaboration depth without hiding those aliases.
    regs = list(doc["registers"].items())
    chunks = []
    for offset in range(0, len(regs), 128):
        name = f"registers_{offset // 128}"
        chunks.append(name)
        out.append(f"def {name} : List (String × Varnode) := [")
        out.append(",\n".join(f"  ({lean_str(n)}, {lean_var(v)})" for n, v in regs[offset:offset + 128]))
        out.append("]")
    out += ["def registers : List (String × Varnode) := [" + ", ".join(chunks) + "].flatten",
            "", "def initialMemory : Memory :="]
    chunks = []
    for region in doc["memory"]:
        raw = bytes.fromhex(region["hex"])
        for offset in range(0, len(raw), 128):
            values = ", ".join(str(b) for b in raw[offset:offset + 128])
            chunks.append(f"  ({region['address'] + offset}, #[{values}])")
    out += ["  ([" + ",\n".join(chunks) + "] : List (Nat × Array Nat)).flatMap fun (base, bytes) =>",
            f"    bytes.toList.zipIdx.map fun (value, i) => (({lean_str(doc['codeSpace'])}, base + i), value)",
            "", "def initialState (entry : Nat) : State := { pc := entry, memory := initialMemory }",
            "", f"end Autoform.Machine.{module}", ""]
    return "\n".join(out)


def coverage(doc: dict) -> dict:
    unsupported = {k: v for k, v in doc["operations"].items() if k not in SUPPORTED}
    return {"instructions": len(doc["instructions"]),
            "instructions_with_unmodelled_ops": sum(any(op["code"] not in SUPPORTED for op in i["ops"])
                                                    for i in doc["instructions"]),
            "operations": sum(doc["operations"].values()), "unsupported_operations": unsupported,
            "decode_errors": doc["decodeErrors"], "loader_gaps": doc["loaderGaps"]}


def render_assertions(doc, module, registers, memory, stops, expected, fuel):
    """Kernel-check caller-supplied, concrete observations of the generated program."""
    if doc["entry"] is None or not stops:
        raise ValueError("--expect requires an entry address (or --entry) and at least one --stop")
    for name in list(registers) + list(expected):
        if name not in doc["registers"]:
            raise ValueError(f"unknown register {name!r} for {doc['language']}")
    lines = [f"namespace Autoform.Machine.{module}.Assertions",
             f"open Autoform.PCode Autoform.Machine.{module}",
             "def assertionState : Except String State := do",
             f"  let s := initialState {doc['entry']}"]
    for spec, value in memory.items():
        parts = spec.split(":")
        if len(parts) != 3:
            raise ValueError("--memory expects SPACE:ADDRESS:BYTES=VALUE")
        space, address, size = parts[0], int(parts[1], 0), int(parts[2], 0)
        if address < 0 or not 1 <= size <= 4096:
            raise ValueError("memory address must be nonnegative, size between 1 and 4096 bytes")
        v = {"space": space, "offset": address, "size": size}
        lines.append(f"  let s ← write program s ({lean_var(v)}) {value % (1 << (8 * size))}")
    for name, value in registers.items():
        v = doc["registers"][name]
        lines.append(f"  let s ← write program s ({lean_var(v)}) {value % (1 << (8 * v['size']))}")
    lines += ["  pure s", "", "def assertionResult : Except String State := do",
              "  let s ← assertionState",
              f"  match run program {stops} {fuel} s with",
              "  | .stopped final => pure final", "  | .hole why _ => throw why",
              '  | .outOfFuel _ => throw "out-of-fuel"', ""]
    for i, (name, value) in enumerate(expected.items()):
        v = doc["registers"][name]
        if not 0 <= value < 1 << (8 * v["size"]):
            raise ValueError(f"--expect {name} requires an unsigned bit pattern fitting {v['size']} bytes")
        lines += [f"def observed_{i} : Except String Nat := do",
                  "  let final ← assertionResult",
                  f"  read program final ({lean_var(v)})",
                  f"theorem checked_{i} : observed_{i} = .ok {value} := by rfl", ""]
    lines.append(f"end Autoform.Machine.{module}.Assertions")
    return "\n".join(lines)


def key_values(items: list[str]) -> dict[str, int]:
    out = {}
    for item in items:
        key, sep, value = item.partition("=")
        if not sep or not key or key in out:
            raise ValueError(f"expected unique NAME=INTEGER, got {item!r}")
        out[key] = int(value, 0)
    return out


def build_model(path: Path) -> None:
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    for command in (["lake", "build", "Autoform.Lang.PCode.Semantics"],
                    ["lake", "env", "lean", str(path)]):
        result = subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True, timeout=1800)
        if result.returncode:
            raise RuntimeError("Lean typecheck failed:\n" + (result.stdout + result.stderr)[-6000:])


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path)
    parser.add_argument("module", nargs="?", default="Machine")
    parser.add_argument("--list-languages", action="store_true")
    parser.add_argument("--language", help="SLEIGH language ID; mandatory for raw bytes")
    parser.add_argument("--format", choices=["auto", "raw", "elf", "pe", "mach-o"], default="auto")
    parser.add_argument("--base", type=lambda s: int(s, 0), default=0)
    parser.add_argument("--entry", type=lambda s: int(s, 0))
    parser.add_argument("--context", action="append", default=[], metavar="NAME=VALUE")
    parser.add_argument("--space-word-size", action="append", default=[], metavar="SPACE=BYTES")
    parser.add_argument("--max-instructions", type=int, default=100000)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--emit-only", action="store_true", help="emit an UNCHECKED model without running Lean")
    parser.add_argument("--assemble", metavar="CLANG_TARGET", help="assemble .s/.S with clang for this explicit target")
    parser.add_argument("--register", action="append", default=[], metavar="NAME=VALUE")
    parser.add_argument("--memory", action="append", default=[], metavar="SPACE:ADDRESS:BYTES=VALUE")
    parser.add_argument("--stop", action="append", default=[], type=lambda s: int(s, 0))
    parser.add_argument("--expect", action="append", default=[], metavar="REGISTER=VALUE",
                        help="emit and kernel-check a concrete final-register assertion")
    parser.add_argument("--fuel", type=int, default=10000)
    args = parser.parse_args(argv)
    report = None
    out = None
    try:
        if args.list_languages:
            import pypcode
            for lang in sorted((lang for arch in pypcode.Arch.enumerate() for lang in arch.languages),
                               key=lambda lang: lang.id):
                print(f"{lang.id}\t{lang.description}")
            return 0
        if not args.input:
            parser.error("input must be an executable, object, raw image, or assembly file")
        if not re.fullmatch(r"[A-Z][A-Za-z0-9_]*", args.module):
            parser.error("module must match [A-Z][A-Za-z0-9_]*")
        if args.max_instructions <= 0 or args.base < 0 or (args.entry is not None and args.entry < 0):
            parser.error("addresses must be nonnegative and --max-instructions positive")
        if args.base and args.format != "raw":
            parser.error("--base applies only to --format raw; executable addresses come from the loader")
        if args.fuel <= 0 or any(v < 0 for v in args.stop):
            parser.error("fuel must be positive and stop addresses nonnegative")
        if (args.register or args.memory or args.stop) and not args.expect:
            parser.error("--register/--memory/--stop are used with --expect")
        units, context = key_values(args.space_word_size), key_values(args.context)
        if any(v <= 0 for v in units.values()):
            parser.error("addressable units must be positive")
        out = (args.out or ROOT / "artifacts" / "machine" / args.module).resolve()
        out.mkdir(parents=True, exist_ok=True)
        # Replace the status first: a failed repeat must not leave yesterday's success.
        report = {"schema": "autoform.machine-report.v1", "status": "FAILED",
                  "input_sha256": None, "module": args.module,
                  "lean_typechecked": False, "source_refinement_proved": False,
                  "property_proved": False}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        # Import after invalidating the report: uninstalling an optional dependency
        # must not leave a previous run's proof status at this output path.
        import pypcode
        if not args.input.is_file():
            raise ValueError(f"input is not a file: {args.input}")
        report["input_sha256"] = sha(args.input)
        with tempfile.TemporaryDirectory(prefix="autoform-machine-") as scratch:
            source = args.input.resolve()
            if args.assemble:
                clang = shutil.which("clang")
                if not clang:
                    raise ValueError("--assemble requires clang on PATH")
                assembled = Path(scratch) / "input.o"
                command = [clang, "-target", args.assemble, "-c", str(source), "-o", str(assembled)]
                proc = subprocess.run(command, capture_output=True, text=True, timeout=120)
                if proc.returncode:
                    raise ValueError("assembler failed:\n" + proc.stderr[-4000:])
                report["assembler"] = {"target": args.assemble, "object_sha256": sha(assembled)}
                source = assembled
            image = load_image(source, args.format, args.language, args.base, args.entry)
            report["machine_code_sha256"] = sha(source)
            doc = lift_image(image, max_instructions=args.max_instructions, space_units=units, context=context)
        report.update(coverage(doc))
        report.update(language=doc["language"], entry=doc["entry"], lifter=doc["lifter"], format=image.format)
        report["assumptions"] = ["SLEIGH lifting is faithful; no verified lifter certificate",
                                 "static instruction decoding; alternate/dynamic modes need explicit context",
                                 "sequential execution; no OS, devices, interrupts, or concurrent memory model",
                                 "ordinary accessible RAM; alignment faults, memory permissions and MMIO are not modelled",
                                 "caller supplies initialized registers, runtime memory and observation addresses"] + image.assumptions
        (out / "pcode.json").write_text(json.dumps(doc, indent=2) + "\n")
        model = out / "Program.lean"
        model.write_text(render_model(doc, args.module), encoding="utf-8")
        check_target = model
        if args.expect:
            registers, memory, expected = key_values(args.register), key_values(args.memory), key_values(args.expect)
            assertions = render_assertions(doc, args.module, registers, memory, args.stop, expected, args.fuel)
            check_target = out / "Check.lean"
            check_target.write_text(model.read_text() + "\n" + assertions, encoding="utf-8")
            report["assertions"] = {"registers": registers, "memory": memory,
                                    "stops": args.stop, "expected": expected, "fuel": args.fuel,
                                    "scope": "supplied concrete initial state only", "proved": False}
        report["pcode_sha256"], report["lean_sha256"] = sha(out / "pcode.json"), sha(model)
        report["semantics_sha256"] = sha(ROOT / "Autoform/Lang/PCode/Semantics.lean")
        report["lean_toolchain"] = (ROOT / "lean-toolchain").read_text().strip()
        report["implementation_sha256"] = {
            str(p): sha(ROOT / p) for p in (
                "Autoform/Lang/PCode/Syntax.lean", "Autoform/Lang/PCode/Semantics.lean",
                "scripts/formalize_machine.py", "scripts/binary_loader.py")}
        if not args.emit_only:
            build_model(check_target)
            report["lean_typechecked"] = True
            if args.expect:
                report["assertions"]["proved"] = True
                report["assertions"]["proof_sha256"] = sha(check_target)
                report["property_proved"] = True
                report["property_scope"] = "supplied concrete initial-state assertions only"
        gaps = bool(report["unsupported_operations"] or report["decode_errors"] or report["loader_gaps"])
        report["status"] = "UNCHECKED" if args.emit_only else ("MODEL_WITH_GAPS" if gaps else "MODEL_TYPECHECKED")
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"{report['status']}: {doc['language']}, {report['instructions']} instructions, "
              f"{report['instructions_with_unmodelled_ops']} with unmodelled operations")
        print(f"Lean model: {model}\nCoverage and assumptions: {out / 'report.json'}")
        if report["property_proved"]:
            print(f"Kernel-checked {len(report['assertions']['expected'])} concrete register assertion(s): {check_target}")
        else:
            print("No behavioral property was proved; use --expect to check a concrete observation.")
        print("Source-to-machine equivalence and lifting faithfulness remain unproved.")
        return 3 if gaps else 0
    except (ImportError, ValueError, RuntimeError, OSError, subprocess.TimeoutExpired) as exc:
        message = str(exc)
        if isinstance(exc, ImportError):
            message += ("\nInstall optional dependencies: python -m pip install 'autoform-lean[machine]'"
                        "\n(from a checkout: python -m pip install -r requirements-machine.txt)")
        if report is not None and out is not None:
            report.update(status="FAILED", error=message)
            (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"formalize_machine: {message}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
