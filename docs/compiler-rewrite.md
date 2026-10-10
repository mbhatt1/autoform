# Compiler simplification

The compiler retains the CPG → JSON AST → Lean Core interface for Python, C, C++,
Java, Go, JavaScript, TypeScript and Kotlin. Existing unsupported constructs remain
labelled holes. The independent SLEIGH/p-code path and the Lean semantics are unchanged.
This is a compatibility-preserving simplification, not a claim that every construct
in those languages is supported or that the implementation is mathematically minimal.

## Implementation

`cartographer/export_ast.sc` is the Joern entry point. It loads
`compiler/SourceCompiler.scala`, which owns a fresh compilation's analysis state,
initializer emission and function lowering. `Json.scala` and `Numeric.scala` hold
encoding and typed numeric operations. Moving code into these files is organization,
not a reduction in the amount of semantic logic.

Duplicate expression construction now shares builders without changing operand
evaluation order, temporary allocation or dialect guards. Python generator and truth
lowering use `cartographer/ast_tools.py` for iterative traversal. The generator pass
still transforms each occurrence; truth passes retain their previous alias policy.
Analysis consumers reuse the existing `analysis_functions` view and keep their own
metrics and source/helper distinctions.

The Lean printer uses constructor descriptions and one iterative document engine.
Flat output, capped layout, child traversal and multiline rendering use that shared
representation, including deeply nested terms. Output compatibility is checked byte
for byte against the previous compiler on tracked AST corpora.

## Reproduction and packages

`scripts/compiler_sources.py` follows Joern's transitive `using file` directives.
Provenance records the digest of every compile unit, and the distribution checker
independently requires that closure in both release artifacts. Existing provenance
is not silently repinned after a compiler change.

`scripts/reproduce_ast.py` honors the selected exporter, verifies that all its compile
units exist, and runs Joern in a temporary working directory. A failed exporter is
a failed reproduction even if it happened to leave matching output.

## Validation

The dated snapshot in `artifacts/compiler-rewrite/validation.json` records commands,
results, source hashes and limitations. Reproduce the main checks with:

```sh
LEAN_NUM_THREADS=1 .venv/bin/python -m pytest tests/ -q
LEAN_NUM_THREADS=1 AUTOFORM_TEST_JOERN=1 .venv/bin/python -m pytest tests/test_source_pipeline.py -q
LEAN_NUM_THREADS=1 ./assure.sh examples/source/python CompilerRewrite
.venv/bin/python -m build --no-isolation
.venv/bin/python scripts/check_distribution.py dist
```

Set `JOERN_HOME` to the installed Joern CLI directory for source checks. Run mutation
assurance in its own checkout: it temporarily changes generated modules and must not
share them with another live proof run.

Source proof harnesses initialize modules before calling functions, as the native
runtime does. To avoid repeatedly reducing that initialization, they propose its
literal state using native execution, then prove the literal equal to `initGlobals`
in the Lean kernel before using it. Expected native results and the original call
fuel remain part of each claim.

The language pipelines exercise fixtures. Byte parity on corpora and successful
fixture proofs do not establish equivalence for arbitrary source programs. Native
inconclusive cases, skips, unsupported constructs and the still-unreproduced corpus
provenance records remain visible in the validation report. The render hashes of the
Python corpora were re-recorded after review (`post_review_2026_09_25` in that file).
