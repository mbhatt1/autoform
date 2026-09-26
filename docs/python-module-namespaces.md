# Python module namespaces

Python source globals belong to the defining module. The exporter reads and writes
that module's object for ordinary global names, explicit `global` assignments and
augmented assignments. A write through `module.name` reaches the same storage as
the defining module's own global read. Function locals and captured bindings keep
their activation or closure storage.

Global callable names are read before evaluating their arguments. A `from` import
stores the member value present when the import statement executes, including
rebound functions and classes. Later replacement of the provider's member does not
replace the importing module's saved binding. Stable lexical classes continue to
use the existing allocation operation; calling an imported class value (or any
other class value) re-dispatches to that same allocation rule in Core
(`Expr.callValue`, `classValueOwner`), so the constructor runs with the arguments
already evaluated once.

Source scope metadata requires both a matching source position and identifier
spelling. Joern's generated temporaries can reuse a source expression's position;
they must retain their temporary binding rather than read the source global again.
Private global names use their lexical class's Python name mangling.

The source fixtures in `examples/python_control/module_namespaces/` compare these
behaviors with CPython and prove the recorded scalar outcomes in the Lean kernel.
Source tests initialize the module objects before calling a function, matching the
native import precondition. Fuel transport keeps that initial state fixed.

This change does not snapshot arbitrary native global state between traced calls,
or implement Python's full import loader or cyclic import execution. Those are
separate boundaries from module namespace isolation.
