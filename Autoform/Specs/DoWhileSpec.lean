import Autoform.Lang.Core.Semantics

/-!
# `do … while` is not `while`

`cartographer/export_ast.sc` mapped both `WHILE` and `DO` to `Stmt.loop`. A do-while runs
its body at least once; `Stmt.loop` tests first. With a condition that is initially false
the two disagree on the first iteration, and the translation type-checked and looked right,
which is how it survived.

Measured with `cc -O0` on x86-64:

```c
int dowhile(void) { int n = 0; do { n = n + 1; } while (0); return n; }   // 1
int whileloop(void){ int n = 0; while (0) { n = n + 1; }   return n; }   // 0
```

The exporter now emits `while (true) { B; if (C) skip else break }` for `DO`, with each
`continue` belonging to that loop rewritten to `if (C) continue else break` — a do-while's
`continue` jumps to the condition test, and the `while (true)` shape has no test to reach.

Every value below is what `cc` printed. `#guard_msgs` fails the build if the semantics
changes and, unlike `native_decide`, introduces no axiom.
-/

namespace Autoform.DoWhileSpec

open Autoform.Core

private def C : Ctx := { dialect := .cLike, table := [], globals := 0 }

/-- `int n = 0; do { n = n + 1; } while (0); return n;` in the shape the exporter now
emits. `cc` prints 1. -/
private def doWhileFalse : Func :=
  { name := "dowhile", params := []
  , body := .seq (.assign "n" (.lit (.int 0)))
             (.seq (.loop (.lit (.bool true))
                     (.seq (.assign "n" (.binop "+" (.name "n") (.lit (.int 1))))
                           (.ifte (.lit (.int 0)) .skip .brk)))
                   (.ret (.name "n"))) }

/-- The same source translated the OLD way, as a plain `while`. `cc` prints 1 for the
do-while; this shape gives 0. It is kept as a negative control: without it, a future
regression to `Stmt.loop` would remove a hole and look like progress. -/
private def asPlainWhile : Func :=
  { name := "aswhile", params := []
  , body := .seq (.assign "n" (.lit (.int 0)))
             (.seq (.loop (.lit (.int 0))
                     (.assign "n" (.binop "+" (.name "n") (.lit (.int 1)))))
                   (.ret (.name "n"))) }

private def run (f : Func) : EResult := (applyFunc C 200 [] f none [] []).2

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 1) -/
#guard_msgs in #eval run doWhileFalse
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 0) -/
#guard_msgs in #eval run asPlainWhile

/-- The two really are different functions, so the fix is not cosmetic. -/
theorem doWhile_differs_from_while :
    run doWhileFalse = .val (.int 1) ∧ run asPlainWhile = .val (.int 0) :=
  ⟨rfl, rfl⟩

end Autoform.DoWhileSpec
