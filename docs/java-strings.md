# Java String model: analysis and cost (2026-10-10)

Status: **not implemented.** A Java `String`/`CharSequence` model cannot be added without
editing `Autoform/Lang/Core`, so by the rule for this work it stops here. Nothing under
`Autoform/Lang/Core` was touched. Numbers below are from `evidence-CommonsLang3.json`
(`inconclusive_by_label`: `call:length` 299 cases / 102 functions, `call:charAt` 7,
`call:toString` 8, `str:reference-equality` 25 / 8 functions).

## 1. What the model must touch

* `Autoform/Lang/Core/Stdlib.lean`: `builtinCore` and `knowsFree` are `none`/`false` for
  `.java`; `methodCore .java` answers only `java.util.List`/`Map` receivers (`add`, `get`,
  `size`, `isEmpty`, `contains`, `put`, `containsKey`). A `.str` receiver has no method.
* `Autoform/Lang/Core/Semantics.lean`: `evalExpr .index` indexes a `.str` only for
  `.javascript`; `applyBinop .java "=="` on two strings is the deliberate hole
  `str:reference-equality` (`stringEqIsReference`); string `+` is a `binop:+` hole.
* The exporter (`cartographer/compiler/SourceCompiler.scala`, outside Core) is also
  involved: for a Java instance call the receiver is at argumentIndex 0 and the generic
  call branch keeps only `argumentIndex >= 1`, so `cs.length()` is exported as
  `call "length" []` and `s.charAt(i)` as `call "charAt" [i]`. The receiver is not in the
  AST at all. (`isEmpty:boolean(CharSequence)` in `ast-CommonsLang3.json` shows it.)
  Core would need the receiver passed as `mcall` receiver or first argument.

## 2. Can it live outside the hashed set?

`scripts/runtime_backends.py::semantics_fingerprints()` hashes every `*.lean` under
`Autoform/Lang/Core` (recursively; this includes the generated `ExternalBases.lean`).
Nothing else is in `semantics_sha256`. `Autoform/Lang/Imp` and `Autoform/Lang/PCode` are
not hashed, and there is no `Autoform/Lang/Java` dialect layer: Java is the `.java`
constructor of `Dialect` inside Core.

Additive routes considered, and why each fails:

1. **Library contracts (`Autoform/Contracts.lean`, docs/contracts.md).** A `Contract`
   assumes a property of a hole inside a refinement proof. It does not change what the
   interpreter returns, and the differential oracle compares the interpreter, so a contract
   moves no function from inconclusive to compared. It would also turn the JVM's String
   behaviour into an assumption, which is the opposite of comparing against the JVM.
2. **Prelude functions in the generated module** (user functions win over builtins in
   `ctx.resolveCall`, so a function named for `String.length` would resolve). Its body
   needs a primitive that reads a `Val.str`. Under `.java` the only string-reading
   primitive is `valIn` (substring test, dialect independent), which gives neither length,
   code unit, prefix nor substring. `Func` has no native-body hook. So the body is not
   expressible.
3. **Re-encode `String` as a list of UTF-16 code units** (lists have `size`/`get`/index
   under `.java`). This needs the exporter to rewrite every string literal, parameter,
   `+`, `==` and return value by type, the harness to encode inputs and decode results,
   and still has no `substring` without boxed mutation. It is a re-encoding of the whole
   Java value domain, not a slice, and a wrong type guess would be an unsound agreement.
   Not attempted.

Answer: **not additive.** The primitives must be added to `Stdlib.lean`/`Semantics.lean`
(`.java` branches for `.str`: `length`, `charAt`, `substring`, `indexOf`, `startsWith`,
`endsWith`, `isEmpty`, `equals`, `toString`, plus value-equality dispatch for
`CharSequence`), and the exporter must keep the receiver.

## 3. Cost of the Core edit

* Every `conformance.json` records `provenance.semantics_sha256`, and
  `load_observations` rejects evidence whose Core hashes differ. All recorded oracle runs
  are therefore invalid: Cachetools, Click, Jinja2, Requests, CommonsLang3, LinuxLcm,
  LinuxLib/LibSample, V8Base (and every module in `Autoform/SpecsGen/*`, whose observation
  theorems are generated from those runs; `scripts/check_specs_fresh.py` fails until they
  are regenerated).
* Each needs `scripts/reland_corpus.sh` (export, render, manifest, provenance, oracle,
  `synth_specs.py`, ledger) and a rebuild of every module downstream of
  `Autoform.Lang.Core.Semantics`. The earlier re-lands in this repository took hours per
  large corpus (one Cachetools spec theorem module alone held 13 to 60 GB and up to 90
  minutes; see `artifacts/interpreter-recovery/corpus-reland-diagnostics.json`), so the
  total is hours of machine time and must be run one build at a time under the heavy
  lock. This is an estimate from those re-lands, not a measurement of this change.
* The exporter change (receiver kept for Java instance calls) additionally changes
  `ast-CommonsLang3.json`, `ast-LangJava.json` and `ast-LangKt.json` (Kotlin rides the
  Java dialect), and these ASTs are not byte-stable across exports (docs/languages.md,
  "The export is not byte-stable").

## 4. Recommended next step

Do it once, as a single Core change batched with the other Core edits that are already
going to force a re-land, so the invalidation is paid once. Order: (a) exporter keeps the
receiver and emits Java String calls under one stable name per method; (b) `.java`
branches in `Stdlib.methodCore`/`Semantics` with UTF-16 code-unit semantics for BMP
strings, and any string containing a surrogate or non-BMP code point answering a hole
(never agreeing); (c) Lean theorems by computation per method on small domains and a JVM
differential test per method; (d) one re-land of CommonsLang3, then the others.
