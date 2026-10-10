# Machine-code formalization

Autoform has two semantic targets. The existing source path maps Joern ASTs into
`Autoform.Core`. The machine path maps SLEIGH raw p-code into `Autoform.PCode`.
The latter avoids assigning source-language arithmetic to machine instructions:
each operand carries its own width, and register aliases share byte storage.

This is a route for compiled languages and assembled code, not a claim that all
languages, processors, or programs are supported. A compiler can connect a source
language to this route, but the resulting theorem concerns the supplied machine
code model. Compiler correctness and source-to-binary correspondence are separate
obligations. Interpreted code requires its runtime or another frontend; passing a
script as raw machine bytes is not a translation of that script.

## Install and run

Use Python 3.10+ and the repository's pinned Lean toolchain. Joern is not required
for this path. The example below selects Python 3.11 explicitly.

```sh
python3.11 -m venv .venv
.venv/bin/python -m pip install -r requirements-machine.txt
./autoform.sh --machine --list-languages
./autoform.sh --machine path/to/executable MyBinary
```

`autoform.sh --machine` uses `.venv/bin/python` when present. Set
`AUTOFORM_PYTHON=/path/to/python` to select another interpreter.

ELF, Mach-O, and PE containers supply executable bytes and virtual addresses.
Architecture inference currently covers x86/x86-64, AArch64, and RISC-V where the
container identifies the mode unambiguously. Other processors require an explicit
SLEIGH language ID; list installed definitions with `--list-languages`. An
available processor definition is **not** a claim that all its instructions are
modelled or tested. Fat Mach-O files must first be reduced to one architecture.

Raw code requires its language and load address:

```sh
./autoform.sh --machine firmware.bin Firmware \
  --format raw --language ARM:LE:32:v8 --base 0x8000000
```

For assembly, name the assembler target rather than guessing from syntax:

```sh
./autoform.sh --machine examples/machine/add_aarch64.s Add \
  --assemble aarch64-unknown-linux-gnu --entry 0 \
  --register x0=3 --register x1=4 --stop 4 --expect x0=7

./autoform.sh --machine examples/machine/add_x86_64.s AddX86 \
  --assemble x86_64-unknown-linux-gnu --entry 0 \
  --register RDI=3 --register RSI=4 --stop 4 --expect RAX=7
```

Other assemblers can supply machine bytes directly. For example, with NASM:

```sh
nasm -f bin examples/machine/add_nasm.asm -o /tmp/add.bin
./autoform.sh --machine /tmp/add.bin NasmAdd \
  --format raw --language x86:LE:64:default \
  --register RDI=3 --register RSI=4 --stop 4 --expect RAX=7
```

These commands assemble, lift, emit an executable Lean program, and kernel-check
the supplied concrete assertion using `rfl`. A false expectation fails the command.
The observation point is before the return instruction, so these examples require
no ABI stack or link-register setup. To run through a return, initialize that state
explicitly, for example `--register RSP=0x8000
--memory ram:0x8000:8=0x9000 --stop 0x9000` on x86-64. Expected values are unsigned
register bit patterns. Registers and memory not initialized remain unknown.

`--expect` proves only the requested observation for the supplied initial state;
it is not a universally quantified specification. Arbitrary Lean specifications
can use the emitted `program`, `initialState`, and `Autoform.PCode.run` directly.
`run_stopped_mono` proves that a successful observation persists with more fuel.

## Artifacts and exit status

The default output directory is `artifacts/machine/<Module>/`; `--out` overrides it.

| Artifact | Content |
|---|---|
| `pcode.json` | Instruction addresses, raw p-code, widths, register locations, initial bytes, decode gaps, processor identity and digest |
| `Program.lean` | Executable model in `Autoform.Machine.<Module>` |
| `Check.lean` | Model and caller-supplied concrete theorems, when `--expect` is present |
| `report.json` | Input/model/semantics digests, coverage, loader gaps, assumptions, typecheck and assertion results |

Exit 0 means the requested emission/check completed without static gaps. It does
not establish behavior for every input. Exit 3 means artifacts were produced with
decode, loader, or operation gaps. Exit 1 means loading, lifting, assembly, or Lean
checking failed. Argument errors exit 2. `--emit-only` explicitly skips Lean and
reports `UNCHECKED`; it never records a proof. A new run invalidates the previous
report before writing artifacts, so a failed repeat cannot reuse a success status.

Models with gaps retain unsupported operations. Execution returns `hole` when it
reaches one, reads uninitialized memory, or branches to absent code. Fuel exhaustion
is a distinct outcome. Only reaching a caller-specified observation address returns
`stopped`; falling off the end of a translated region is not success.

## Implemented semantics and validation

The interpreter implements raw p-code integer and boolean operations, sign/zero
extension, shifts, carry/overflow flags, concatenation/extraction, bit counts,
byte-addressed register aliasing, little/big endian memory, direct/indirect control
flow, and intra-instruction branches. Calls and returns follow raw p-code: the
other operations in an instruction implement its stack or link-register effects.
Unique temporaries are cleared at machine-instruction boundaries. Delay-slot
operations stay attached to the instruction that executes them.

Tests execute generated models for x86-64, AArch64, RISC-V, and big-endian MIPS.
They cover wraparound, signed operations, memory, subregister updates, delay slots,
failure outcomes, and kernel acceptance/rejection of concrete assertions. Native
conformance compares compiler-generated arithmetic, branch/division, and loop
routines against execution on the host CPU. The host oracle covers the host ISA;
the other ISA tests are known-result checks, not hardware conformance claims.

```sh
.venv/bin/python -m pip install 'pytest>=8,<9'
.venv/bin/python -m pytest tests/test_machine_frontend.py -q
lake build Autoform.Lang.PCode.Properties
lake env leanchecker --fresh Autoform.Lang.PCode.Properties
```

## Remaining work toward arbitrary codebases

* **Build and frontend coverage:** this path takes a supplied native binary or
  assembly accepted by an explicitly selected clang target. It does not discover
  and build arbitrary repositories, translate every assembler syntax, or provide
  JVM, CLR, WebAssembly, and language-runtime adapters.
* **Lifter correctness:** SLEIGH processor descriptions and pypcode are unverified
  translation dependencies. Pinning and hashing them provides reproducibility,
  not a proof that their semantics match hardware.
* **Instruction coverage:** floating-point p-code, processor-specific `CALLOTHER`
  operations, privileged instructions, and decompiler-only operations remain
  holes. Vector operations work only where SLEIGH lowers them entirely into the
  implemented integer operations; no general SIMD claim is made.
* **Environment:** no operating system, dynamic linker, syscall/device model,
  interrupt model, concurrent memory model, or inferred calling convention.
  Runtime loader gaps are reported, and initial bytes needing fixups are withheld.
  Unapplied code relocations block execution before instruction effects. Data-only
  relocations withhold initial memory; an independent register-only function can
  still be checked, while reads from unresolved data stop at a hole. Link objects
  before making claims about a complete executable.
* **Decoding:** static linear decoding cannot discover every computed branch,
  distinguish all inline data, or recover self-modifying/JIT code. Unknown decoding
  stops the region and records its remaining bytes. Writes over lifted instructions
  are holes. `--context NAME=VALUE` sets an explicit SLEIGH mode; dynamic mode
  transitions are not generally modelled.
* **Address spaces:** known byte-addressed processor families have a RAM unit of
  one byte. Other LOAD/STORE spaces need `--space-word-size SPACE=BYTES`.
  Word-addressed indirect control flow and address-space wraparound remain holes.
  Memory permission faults, MMIO and alignment traps are not modelled.
* **Scale:** `--max-instructions` bounds translation and reports a gap when reached.
  The executable model currently uses list-based lookup and a sparse byte store;
  large whole-program proofs need better indexing and compositional reasoning.
* **Assurance integration:** machine models have their own coverage and proof
  reports. The source pipeline's `assure.sh` and SACM generator do not yet consume
  those reports or compose claims across source and machine models.
* **Specification discovery:** code alone cannot determine its intended behavior.
  Supplied contracts, environmental assumptions, and independently checked
  specifications remain necessary for meaningful program correctness claims.

The source path also has remaining semantic gaps. In particular, a shared `.cLike`
dialect does not faithfully cover every Java/Go/C++ numeric type. Mixed dialects and
unrecognized source extensions now fail instead of being resolved by majority vote.
See the historical measurements in [languages.md](languages.md).

The implementation follows the official [Ghidra raw p-code reference](https://ghidra.re/ghidra_docs/languages/html/pcoderef.html)
and [operation definitions](https://ghidra.re/ghidra_docs/languages/html/pcodedescription.html),
using the [pypcode API](https://docs.angr.io/projects/pypcode/en/v3.3.0/api.html).
