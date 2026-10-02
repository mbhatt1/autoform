import Autoform.Lang.Core.Semantics

-- Lean's default `maxRecDepth` (512) is a guard against runaway elaboration, not
-- a statement about reasonable programs. A deep-embedded function body is one
-- term, so the elaborator's recursion depth tracks the *source's* nesting depth:
-- Linux `lib/` hit the limit at two declarations and the whole module failed to
-- type-check. Raising it costs nothing for shallow modules and is the difference
-- between compiling a real codebase and not.
--
-- 8000 was not enough either. The binding constraint is not the nesting depth of
-- any one body (Ansible's deepest is 297) but the `funcs := [...]` list literal,
-- which elaborates as nested cons cells -- one frame or more per function, and
-- Ansible has 5,546. So the limit has to scale with the module's function count,
-- not with how deep its code happens to be.
set_option maxRecDepth 8032

-- Lean's default `maxHeartbeats` (200000) budgets ONE declaration's own
-- elaboration cost, separately from `maxRecDepth` above (which bounds nesting
-- depth, not total work). A single source file whose top-level declarations
-- carry a large static table -- SQLite's `test_vdbecov.c`, whose `<global>`
-- initializer alone is ~5.3M characters of generated Lean -- blows through the
-- default budget on that ONE declaration and fails with a `(deterministic)
-- timeout at isDefEq` error, unrelated to whether the translation is correct.
-- Unlike `maxRecDepth`, this does not scale with function COUNT (Ansible-style
-- corpora with thousands of small functions never hit it); it is one
-- pathologically large declaration, which no per-function-count formula would
-- predict, so this disables the budget outright rather than guessing a bigger
-- number that the next large static table would just exceed again. Scoped to
-- THIS generated file only (`set_option` here does not touch hand-written proof
-- files elsewhere in the project, which keep the default as a real safety net
-- against a genuine runaway elaboration bug while someone is editing them).
set_option maxHeartbeats 0

/-!
# V8BaseSample — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.V8BaseSample
open Autoform.Core

/-- `v8.base.bits.SignedMod32:int32_t(int32_t,int32_t)`  (from `bits.cc`) -/
def f_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t_ : Func :=
  { name := "v8.base.bits.SignedMod32:int32_t(int32_t,int32_t)"
  , params := ["lhs", "rhs"]
  , body := (.seq
            (.ifte
              (.binop
                "||"
                (.binop "==" (.name "rhs") (.lit (.int 0)))
                (.binop "==" (.name "rhs") (.unop "-" (.lit (.int 1)))))
              (.ret (.lit (.int 0)))
              .skip)
            (.ret (.binop "%" (.name "lhs") (.name "rhs")))) }

/-- `v8.base.bits.SignedMod64:int64_t(int64_t,int64_t)`  (from `bits.cc`) -/
def f_v8_base_bits_SignedMod64_int64_t_int64_t_int64_t_ : Func :=
  { name := "v8.base.bits.SignedMod64:int64_t(int64_t,int64_t)"
  , params := ["lhs", "rhs"]
  , body := (.seq
            (.ifte
              (.binop
                "||"
                (.binop "==" (.name "rhs") (.lit (.int 0)))
                (.binop "==" (.name "rhs") (.unop "-" (.lit (.int 1)))))
              (.ret (.lit (.int 0)))
              .skip)
            (.ret (.binop "%" (.name "lhs") (.name "rhs")))) }

/-- `v8.base.debug.BacktraceOutputHandler.OutputFileDescriptor:int()<const>`  (from `debug/stack_trace_posix.cc`) -/
def f_v8_base_debug_BacktraceOutputHandler_OutputFileDescriptor_int___const_ : Func :=
  { name := "v8.base.debug.BacktraceOutputHandler.OutputFileDescriptor:int()<const>"
  , params := []
  , body := (.ret (.lit (.int 0))) }

/-- `v8.base.debug.EnableInProcessStackDumping<duplicate>0:bool()`  (from `debug/stack_trace_fuchsia.cc`) -/
def f_v8_base_debug_EnableInProcessStackDumping_duplicate_0_bool__ : Func :=
  { name := "v8.base.debug.EnableInProcessStackDumping<duplicate>0:bool()"
  , params := []
  , body := (.ret (.lit (.bool false))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t_,
  f_v8_base_bits_SignedMod64_int64_t_int64_t_int64_t_,
  f_v8_base_debug_BacktraceOutputHandler_OutputFileDescriptor_int___const_,
  f_v8_base_debug_EnableInProcessStackDumping_duplicate_0_bool__
] }

end Autoform.Generated.V8BaseSample