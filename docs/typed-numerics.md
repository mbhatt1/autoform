# Numeric semantics through Joern

`cartographer/export_ast.sc` preserves the source language and promoted integer
type in Core operator names: `num:java:i64:+`, `num:go:u64:<<`,
`num:c:u32:<`, and `num:js:i32:>>>`, for example. The existing neutral AST,
renderer, and interpreter remain the pipeline. No additional source parser is used.

`Autoform/Lang/Core/TypedNumeric.lean` interprets these operators using the existing
`NumConfig`, `IntType`, and kernel-reducible floating-point model. Untagged operators
in older AST artifacts retain their previous dialect semantics; regenerate an AST
with Joern to obtain the new type information.

The exporter derives C integer promotions from operand types when Joern reports
the expression result as `ANY`. Java operations promote byte/short/char to int and
preserve long operands. Go operations preserve their declared integer width, with
integer constants converted to the other operand's type. Integer assignments,
compound assignments and increments convert the result to the known destination
type. C arithmetic conditional expressions convert the selected branch to their
common type before an enclosing operation consumes it. Unresolved scalar
arithmetic produces `numeric:unknown-type:<op>` rather than assuming int32.
C integer literals use their magnitude, radix, suffix, and target model: Joern
can report an out-of-range literal as `int`. Its unnamed `void` parameter for
`f(void)` is also removed, so the translated function correctly takes no arguments.

Joern's `<operator>` and `<operators>` spellings are normalized at the exporter
boundary, including compound bitwise and remainder assignments. Lifted condition
effects run at each loop test and on the appropriate `continue` paths. Logical
`&&` and `||` keep right-hand effects on the selected branch. Binary operands are
saved before later lifted effects can overwrite their values. The same sequencing
applies to ordinary call arguments and indexed reads. Compound assignments in
Python, Java and JavaScript save the old value before lifted right-hand effects;
field updates also retain the original receiver. C/C++ aggregate boxing is
restricted to those languages so that it cannot discard Python object construction
or alias assignments. Explicit integer casts use the source language's type rules,
including Java's byte and char widths.

For a C struct defined inside a function, Joern can omit its member declarations.
The exporter recovers complete, plain integer fields from that local's CPG source
span and keys them by the declaring variable. This supports field-width conversion
without sharing a tag's definition across functions. Nested aggregates, bitfields,
attributes, pointer fields and ambiguous declarations are not recovered this way.

The tagged interpreter covers integer arithmetic, comparisons, bitwise operators,
and shifts. Java masks shift counts and wraps overflow. Go wraps overflow,
including minimum-integer division by -1, and permits shift counts larger than
the word width. C signed arithmetic overflow and invalid shifts produce `ub:*`
holes. C negative signed right shifts retain the existing arithmetic-shift target
assumption. Java and JS right-shift tokens are checked against the CPG child source
text because Joern can use either right-shift operator name for both `>>` and `>>>`.
Grouping parentheses are accepted only when both complete child expressions match
the surrounding source; a nested shift token cannot determine its parent's operator.

JS bitwise operations coerce Number values to 32 bits, including binary64 rounding,
truncation, NaN, and infinity; `>>>` returns an unsigned result. String/object
coercion remains a hole. This does not implement BigInt or fix ordinary JS Number
arithmetic beyond the safe-integer range.

`AUTOFORM_DATA_MODEL=lp64` is the source CLI default. Set it to `llp64` or `ilp32`
for the appropriate target, or `unknown` to refuse target-sized types. The same
choice is available directly as `--param dataModel=...` to the Joern exporter.
Fixed-width integer types are independent of this setting. This parameter does
not claim to describe every ABI, C integer representation, enum layout, or compiler
flag. Function-boundary conversions, assignments with unresolved destination types,
floating-point promotion, general callee/receiver and assignment evaluation order, unsequenced C effects,
user-defined operators, and other languages still need separate semantic work.
The Go fixtures cover constant arithmetic and shifts whose
width comes from the return context. Unresolved constant or contextual types remain
holes. Parsing a language with Joern is not proof of its coverage.

Generated conformance proofs stage execution before comparing observations. They
use kernel reduction with a proof-producing `cbv` fallback for expensive bitwise
reductions; no native-evaluation axiom is introduced. The axiom audit and independent
kernel replay check this on the emitted modules.

Run kernel boundary/refusal checks:

```sh
python3 -m pytest tests/test_source_numeric.py::test_typed_numeric_kernel -q
```

Run the source → CPG → JSON → Lean comparisons against CPython, Java, Go, C, and Node:

```sh
AUTOFORM_TEST_JOERN=1 python3 -m pytest tests/test_source_numeric.py -q
```

The test requires Joern, Lean, `java`/`javac`, `go`, `cc`, and `node`. `JOERN_HOME`
accepts the install root or its `joern-cli` directory. It builds current semantics
before comparing and checks a representative translated claim by kernel reduction.
These fixtures establish numeric behavior for the tested operations, not whole
language or whole-codebase equivalence.

The native corpus also retains strict expected-failure tests for JavaScript array
construction and string indexing. Those cases remain unverified and are excluded
from agreement counts. JavaScript arrays require reference identity and aliasing;
string indexing requires UTF-16 semantics. Python list indexing has a separate
regression for replacing the container while evaluating the index.
Python list and tuple indices are adjusted relative to their length when negative,
then checked against both bounds before conversion to a natural number. Out-of-range
indices raise `IndexError`; very large negative integers cannot clamp to element zero.
The sequence-boundary kernel test derives its expected outcomes from CPython and
runs without Joern.

Language rules: [Java numeric operators](https://docs.oracle.com/javase/specs/jls/se25/html/jls-15.html#jls-15.17),
[C conditional and assignment conversions](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf),
[C++ integer literal types](https://eel.is/c++draft/lex.icon),
[Go integer operators](https://go.dev/ref/spec#Integer_operators), and
[ECMAScript ToInt32](https://tc39.es/ecma262/multipage/abstract-operations.html#sec-toint32).

## The differential suite, run across every language

`tests/test_source_numeric.py::test_joern_native_numeric` is parameterised over the
language matrix and gated behind `AUTOFORM_TEST_JOERN=1`, so it does not run in an
ordinary `pytest` invocation — it parses with Joern, exports, renders, and compares
against the real runtime for each language. Run in full (Joern 4.0.606, `cc`, `node`,
`javac`, `go`):

    5 passed, 2 xfailed

**No open numeric divergence.** Every arithmetic, shift, bitwise, short-circuit,
assignment-order and call-order case in the matrix agrees with its native runtime. That
is a measurement, not an absence of reports: "no known divergence" and "the suite was run
and says so" are different claims, and only the second one is evidence.

The two `xfail`s are `strict`, so they would fail the suite if they started passing, and
neither is numeric:

* **`indexSnapshot`** — JavaScript array literals need reference and identity semantics.
  This is now *closer* than the reason recorded against it. The JS frontend lowers
  `[a, b]` to `__ecma.Array.factory()` followed by `.push(a)`, `.push(b)`, which is
  exactly the mutable-container idiom `docs/boxed-containers.md` now implements — a boxed
  `Obj` with a `.list` payload, mutated in place. Three things remain, and none is
  aliasing: `__ecma.Array.factory()` must translate to an empty boxed array; the boxing
  gate in `evalExpr` must admit `.javascript` as well as `.python` (JS arrays are
  reference types, so this is correct rather than convenient); and `push` needs
  JavaScript semantics — it returns the new **length**, where Python's `append` returns
  `None`, so `Stdlib.method` cannot simply be routed there for `.javascript`.
* **`indexString`** — UTF-16 string indexing, which is a separate representation question
  and unrelated to containers.

