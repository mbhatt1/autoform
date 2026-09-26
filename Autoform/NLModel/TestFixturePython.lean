import Autoform.Lang.Core.Semantics

/-!
# TestFixturePython — hand-written stand-in for an AI-written model (tests only)

Shaped like the modules the `model` stage of the natural-language autoformalizer emits
(`src/autoform/nl/model.py`): one plain Lean `def` per function of
`examples/source/python/numbers.py`, and a dispatcher `call` that decodes `Val` arguments,
runs the def and encodes the result (a raised exception is `.exn (.str "<Class>")`).
`tests/test_nl_refine.py` proves `call` equal to the deep translation
`Autoform.Generated.PipelinePython` (the L1 step, `src/autoform/nl/refine.py`).
-/

namespace Autoform.NLModel.TestFixturePython
open Autoform.Core

/-- `add(a, b)`: `a + b` on Python ints. -/
def add (a b : Int) : Int := a + b

/-- `quotient(a, b)`: Python floor division; `ZeroDivisionError` when `b = 0`. -/
def quotient (a b : Int) : Except String Int :=
  if b = 0 then .error "ZeroDivisionError" else .ok (Int.fdiv a b)

/-- Dispatcher: function name and `Val` arguments to an `EResult`. -/
def call : String → List Val → EResult
  | "numbers.py:<module>.add", [.int a, .int b] => .val (.int (add a b))
  | "numbers.py:<module>.quotient", [.int a, .int b] =>
      match quotient a b with
      | .ok r => .val (.int r)
      | .error e => .exn (.str e)
  | name, _ => .hole s!"nlmodel:{name}"

end Autoform.NLModel.TestFixturePython
