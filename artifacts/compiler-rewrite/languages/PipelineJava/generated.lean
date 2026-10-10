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
set_option maxRecDepth 8056

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
# PipelineJava — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.PipelineJava
open Autoform.Core

/-- `Numbers.add:long(long,long)`  (from `Numbers.java`) -/
def f_Numbers_add_long_long_long_ : Func :=
  { name := "Numbers.add:long(long,long)"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:java:i64:+" (.name "a") (.name "b"))) }

/-- `Numbers.div:long(long,long)`  (from `Numbers.java`) -/
def f_Numbers_div_long_long_long_ : Func :=
  { name := "Numbers.div:long(long,long)"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:java:i64:/" (.name "a") (.name "b"))) }

/-- `Numbers.shift:int(int,int)`  (from `Numbers.java`) -/
def f_Numbers_shift_int_int_int_ : Func :=
  { name := "Numbers.shift:int(int,int)"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:java:i32:<<" (.name "a") (.name "b"))) }

/-- `Numbers.unsigned:long(long,int)`  (from `Numbers.java`) -/
def f_Numbers_unsigned_long_long_int_ : Func :=
  { name := "Numbers.unsigned:long(long,int)"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:java:i64:>>>" (.name "a") (.name "b"))) }

/-- `Numbers.inc:long(long)`  (from `Numbers.java`) -/
def f_Numbers_inc_long_long_ : Func :=
  { name := "Numbers.inc:long(long)"
  , params := ["a"]
  , body := (.seq
            (.assign "a" (.unop "cast:i64" (.binop "num:java:i64:+" (.name "a") (.lit (.int 1)))))
            (.ret (.name "a"))) }

/-- `Numbers.bump:byte(byte)`  (from `Numbers.java`) -/
def f_Numbers_bump_byte_byte_ : Func :=
  { name := "Numbers.bump:byte(byte)"
  , params := ["a"]
  , body := (.seq
            (.assign "a" (.unop "cast:i8" (.binop "num:java:i32:+" (.name "a") (.lit (.int 1)))))
            (.ret (.name "a"))) }

/-- `Numbers.compound:byte(byte,int)`  (from `Numbers.java`) -/
def f_Numbers_compound_byte_byte_int_ : Func :=
  { name := "Numbers.compound:byte(byte,int)"
  , params := ["a", "b"]
  , body := (.seq
            (.assign "a" (.unop "cast:i8" (.binop "num:java:i32:+" (.name "a") (.name "b"))))
            (.ret (.name "a"))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.java` (integer division/modulo convention). -/
def program : Program := { dialect := .java, funcs := [
  f_Numbers_add_long_long_long_,
  f_Numbers_div_long_long_long_,
  f_Numbers_shift_int_int_int_,
  f_Numbers_unsigned_long_long_int_,
  f_Numbers_inc_long_long_,
  f_Numbers_bump_byte_byte_,
  f_Numbers_compound_byte_byte_int_
] }

end Autoform.Generated.PipelineJava