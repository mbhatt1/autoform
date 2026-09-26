# Native heap observations

The `heap-graph-v1` measurement basis records a call's input heap, outcome and final
heap. A cell contains a class identity, named fields and an optional list or dictionary
payload. Mutable containers and ordinary instances share one reference namespace.
The input snapshot is retained separately from live objects, so mutations cannot
rewrite the input evidence. A post-state that cannot be encoded makes the observation
unavailable; it does not become a return-only observation.

`Autoform.Core.HeapObservation.compare` checks the recorded outcome and every object
reachable from the input receiver or arguments. It also follows objects newly reachable
from those objects or the return value. An input object is still checked after the call
detaches it, because another caller reference may retain it. Initial addresses are
fixed. Fresh addresses are matched injectively in both directions, preserving aliases
and terminating on cycles through a visited set. Unreachable interpreter allocations
do not affect the comparison.

The comparison preserves scalar kinds, floating-point bits, named object fields,
container kinds, list order and dictionary insertion order. It compares object fields
by name, using the first stored binding just as Core's attribute reader does. Older
shadowed bindings are internal storage rather than additional Python attributes.
Globals outside the observed roots, mutable class namespaces, immutable-value
identity and the insertion order of instance dictionaries are outside this observation.
Core's internal mutation version is also outside native observations; the separate
`lawHeapPreserved` predicate compares it as part of exact interpreter state.

Plain function values require a unique exported source location outside a function body
or loop, no captures, defaults,
annotations or custom attributes, and unchanged function state through the call.
Function names must be exact strings; module and documentation metadata must be exact
strings or `None`. Mutable metadata, injected mutable code constants and deferred
annotation evaluators are refused before metadata comparison or annotation evaluation.
Replacing a code object is a state change even if the replacement compares equal.
Unresolved callables, external object storage and mutable container subclasses are
refused. A local function is refused even without captures: separate executions can
create distinct function objects that share the same code location. Two distinct
observed function objects may never share one exported identity, including objects
created by module reexecution or `types.FunctionType`. A class value
denotes its exact qualified declaration, not a snapshot of its
class namespace.

The checker uses structural recursion over a comparison budget. Exhaustion is an
unanswered comparison, never agreement. Generated `Obs` values carry the final graph;
`lawConform` checks it together with the return or exception. Staged proofs must establish
the complete resulting heap and outcome before checking the graph. Historical records
without this measurement basis retain their explicitly weaker return-only meaning.

The implementation follows Python's documented distinction between object identity and
mutable contents ([data model](https://docs.python.org/3.11/reference/datamodel.html#objects-values-and-types))
and uses recursion that Lean can reduce in the kernel
([Lean reference](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#structural-recursion)).
