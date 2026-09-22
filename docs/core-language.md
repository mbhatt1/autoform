# The Core language

`Autoform.Core` is the deep-embedded universal imperative language that every translated
codebase is mapped onto. Coverage, conformance, refinement and the trust ledger are all
statements about terms of these types and about the interpreter that runs them.

Source of truth: `Autoform/Lang/Core/Syntax.lean` and `Autoform/Lang/Core/Semantics.lean`.
Where this document and the source disagree, the source is right and this document is a
bug. Nothing here restates a number; the shapes are stable, the counts are not.

Core is shaped to match **Joern's CPG node vocabulary**, not any one language's grammar.
That is why one semantics can cover C, C++, Java, JavaScript, Python and Kotlin: the front
ends have already normalized to a common vocabulary, so Core only has to be faithful to
*that*.

---

## 1. Values (`Val`)

| Constructor | Meaning |
|---|---|
| `int : Int → Val` | An integer. Width and overflow are **not** properties of the value — they belong to `NumConfig`, selected by the dialect. A `Val.int` is always the mathematical integer that the configured arithmetic produced. |
| `str : String → Val` | A string *or* a C `char*`. One constructor: see §7, where the operators are dialect-split instead. |
| `bool : Bool → Val` | A boolean. |
| `float : Fl → Val` | A floating-point bit pattern and format, interpreted by the kernel-reducible model in `Float.lean`. |
| `unit : Val` | The absence of a value: an unbound name, a function that fell off the end, an absent field. |
| `list : List Val → Val` | An immutable list value. Python list literals allocate a `ref` to an object with a mutable list payload; `Stmt.setIndex` updates that payload. |
| `tuple : List Val → Val` | A tuple. Same immutability. |
| `dict : List (Val × Val) → Val` | An association list, *not* a hash map. Key order is observable in real languages and differs between them, so imposing one language's iteration order would be an invented answer. |
| `ref : Ref → Val` | A reference to a heap object. Reference identity is what `is` compares. |
| `fn : String → Val` | A function, method or class used as a value (CPG `METHOD_REF` / `TYPE_REF`). |
| `clos : String → List (String × Val) → Val` | A closure: a function name plus the bindings it captured. Capture is **by value**. |
| `clsClos : String → List (String × Val) → Val` | A *class* value that captured an enclosing scope. Distinct from `clos` because a class is not a function: its methods, not it, read the captured bindings. |
| `bobj : String → Val → Val` | An instance of a class whose **base is a builtin type** (`class X(tuple)`, `(list)`, `(dict)`, `(str)`): the class name plus the underlying builtin value. It compares, iterates, indexes and tests membership as the builtin does, which makes `hashkey(0) == (0,)` true as it is in CPython. It has **no mutable attributes** — a `bobj` is a value, not a heap object — so `e.f` on one is a hole. Which classes get one is recorded per program in `Program.builtinBases`; a class the exporter did not record stays an opaque `ref`. See `Autoform/BuiltinBase.lean`. |

Three derived functions:

* `Val.truthy` — the permissive truthiness shared by most dynamic languages (empty
  containers, `0`, `""` and `unit` are false; references and callables are true).
* `Val.iterable` — the elements of a list, tuple, dictionary or string (or a `bobj`
  over one). It returns `none` for other values; `forIn` additionally dispatches Python
  iterator and sequence protocols for heap objects.
* `Val.unbuiltin` — strips one layer of builtin-base wrapping. Non-recursive, so the
  functions that use it stay plain matchers that reduce by `rfl`.

Python `any`/`all` use a Core consumer that dispatches declared truth methods and reads
boxed container contents. `Val.truthy` itself does not execute those methods; its use
elsewhere does not establish complete Python truth-protocol coverage.

`Val.beq` is hand-written structural equality (the nested `List`/`Prod` occurrences block
`deriving DecidableEq`). Closures and class closures compare by *name only*, ignoring
captured environments.

A `bobj` compares by its **contents, ignoring the class**, and compares equal to the plain
builtin: CPython's `tuple.__eq__` does the same, and `A((0,)) == B((0,))` is `True` there
for two distinct subclasses of `tuple`. That is sound only because `Expr.alloc` *refuses*
to build a `bobj` for a class that defines its own `__eq__` (or its own `__init__`),
emitting `alloc:builtin-base:<cls>:own-__eq__` instead — `Val.beq` has no dunder dispatch,
so honouring such a class would mean silently ignoring the override.

`Autoform/Lang/Core/Float.lean` is wired into `Val` and Core operations. This does
not establish complete source-language floating-point coverage: unsupported literal
forms, conversions and runtime value encodings can still produce holes or skips.
See [typed numerics](typed-numerics.md) for the tested source behavior.

## 2. The memory model: `Heap`, `Obj`, `Env`, `Ctx`

```lean
abbrev Ref  := Nat
structure Obj where cls : String; fields : List (String × Val); captured : List (String × Val)
abbrev Heap := List Obj                 -- index into the list is the Ref; alloc appends
abbrev Env  := List (String × Val)      -- local variables; `set` conses, shadowing
structure Ctx where dialect : Dialect; table : FuncTable; globals : Ref
```

* **Objects are the only mutable things.** Everything else is a value. Field writes go
  through `Heap.setField`, which conses a new binding onto the object's field list.
* **Reads of absent things are `unit`** at the heap level: `Env.get` on an unbound name,
  `Heap.getField` on an absent field, `Heap.get` on a dangling ref. `Expr.field` layers
  the language rule on top: under `.python` an attribute that is found nowhere raises
  `AttributeError` (Language Reference §3.2.11/§3.3.2, `docs/languages.md` §16.A); under
  `.javascript` it is `undefined` = `unit` (ECMA-262 OrdinaryGet). The differential oracle
  is what settled the Python answer (private name mangling was the first bug it found
  here, a missing attribute answering `unit` the latest).
* **Field lookup order** (`Expr.field`) is the object's own fields, then the bindings its
  class captured, then a `@property` getter, then a class attribute; after that,
  `AttributeError` under `.python` and `unit` elsewhere.
* **Globals live on the heap, not in `Env`.** Module-level bindings must be mutable and
  must outlive any single call, so they occupy a distinguished object (`cls = "<globals>"`)
  at `Ctx.globals`. `runMain` allocates it first, so it is ref 0, and any harness building
  its own heap must allocate fresh objects from `heap.length` onward.
* **The heap is threaded explicitly** through `evalExpr`/`execStmt` rather than hidden in a
  monad. That cost keeps the fuel recursion visibly structural, so Lean accepts the
  interpreter as total without `partial`.
* **`Ctx.resolve` falls back from exact name to *unique* suffix match**, because Joern emits
  fully-qualified names (`pkg/mod.py:<module>.Cls.meth`) while call sites carry short ones.
  This is a heuristic, written so that an *ambiguous* match resolves to a hole rather than
  to a guess. `Ctx.resolveMethod` prefers `Cls.meth` and falls back to any `.meth`.

## 3. Expressions (`Expr`)

| Constructor | Meaning |
|---|---|
| `lit : Lit → Expr` | An `int` / `str` / `bool` / `float` / `unit` literal. |
| `name : String → Expr` | Variable read. Resolution order: local `Env`, then the globals frame, then the function table (yielding `Val.fn`), then `unit`. The function-table fallback is what makes higher-order code translatable instead of holed. |
| `binop : String → Expr → Expr → Expr` | Binary operator by name. `&&`/`\|\|` short-circuit (§5); everything else evaluates left then right. |
| `unop : String → Expr → Expr` | Unary operator by name (`-`, `!`). |
| `call : String → List Expr → Expr` | Call by name. Tries `Ctx.resolve`, then a `Val.fn`/`Val.clos` held in a variable, then the modelled stdlib, then a `call:<name>` hole. The stdlib is consulted **last** so a user function of the same name always wins. |
| `index : Expr → Expr → Expr` | Subscript. Out-of-range list/tuple index raises `IndexError`; a missing dict key raises `KeyError`. Under `.python`, on an ordinary instance whose class defines `__getitem__`, it IS `c.__getitem__(k)` (`Ctx.dunderOn`); anything else is `index:unsupported`. |
| `field : Expr → String → Expr` | Attribute read. A non-reference receiver is `field:<f>:non-object`. |
| `mcall : Expr → String → List Expr → Expr` | Method call, dispatched on the receiver's class. A non-object receiver falls through to the modelled stdlib's container methods; a *mutating* container method is `mcall:<m>:unboxed-container` because writing back through the receiver expression would update a temporary. |
| `alloc : String → List Expr → Expr` | Construction. Allocates a fresh object, copies in any bindings the class captured, and runs `__init__` if one resolves. |
| `fnref : String → Expr` | A function, method or class as a value. |
| `closure : String → Expr` | A function value that captures the current `Env` by value: decorators, factories, nested functions reading outer variables. |
| `classClosure : String → Expr` | A class value that captures the current `Env`; instances carry those bindings so their methods can read the enclosing scope. |
| `listE` / `tupleE` / `dictE` | Container literals. |
| `cond : Expr → Expr → Expr → Expr` | Conditional expression; only the taken branch is evaluated. |
| `isOp : Bool → Expr → Expr → Expr` | Identity. Reference identity for `.ref`, structural for immediates. The `Bool` means negated (`is not`). |
| `inOp : Bool → Expr → Expr → Expr` | Membership over lists, tuples, dict keys, and substrings; under `.python`, on an ordinary instance whose class defines `__contains__`, it IS `c.__contains__(x)` and `not in` negates that result's truthiness. The `Bool` means negated (`not in`). |
| `hole : String → Expr` | An unmapped expression, tagged with the CPG node label that produced it. |

## 4. Statements (`Stmt`)

| Constructor | Meaning |
|---|---|
| `skip` | No-op. |
| `expr : Expr → Stmt` | Evaluate for effect; discard the value (but not exceptions or holes). |
| `assign : String → Expr → Stmt` | Local binding — unless a `declGlobal` marker for that name is in scope, in which case it writes the globals frame. |
| `setField : Expr → String → Expr → Stmt` | `e.f = v`. Non-object receiver: `setField:<f>:non-object`. |
| `setIndex : Expr → Expr → Expr → Stmt` | `e[i] = v`. Writes through a boxed list or dict payload (`docs/boxed-containers.md`); under `.python`, on an ordinary instance whose class defines `__setitem__`, it IS `c.__setitem__(i, v)`. A container *value* (a C aggregate) or an instance without the method is the hole `setIndex:immutable-containers`. |
| `delIndex : Expr → Expr → Stmt` | `del e[i]`. The same shape as `setIndex` one argument shorter: payload deletion, or `c.__delitem__(i)` under `.python` when the class defines it, else `delIndex:immutable-containers`. |
| `seq : Stmt → Stmt → Stmt` | Sequencing. Only a `normal` outcome continues. |
| `ifte` / `loop` | Conditional and `while`. |
| `forIn : String → Expr → Stmt → Stmt` | Python uses live container iteration or the instance iterator/sequence protocol; unboxed sequences use `Val.iterable`. Unsupported non-iterables are `forIn:non-iterable`. Joern desugars Python `for` and comprehensions into an iterator protocol plus a `WHILE`; the exporter reconstructs `forIn` from that shape. |
| `ret` / `brk` / `cont` | Return, break, continue — each its own `Ctl` outcome. |
| `tryCatch : Stmt → String → Stmt → Stmt` | `try/except as x`. Catches **exceptions only**: `ret`/`brk`/`cont` pass straight through, or every `try` containing a `return` would break. |
| `tryFinally : Stmt → Stmt → Stmt` | The finalizer runs on every language-level exit, using the locals at that point. Its assignments survive resuming a pending exit; its own abnormal exit replaces the pending outcome. Interpreter holes and exhausted fuel propagate without running the finalizer — Python's rule, so `try: return 1 finally: return 2` returns 2. |
| `raise : Expr → Stmt` | Raise the evaluated value as an exception. |
| `del : String → Stmt` | Remove every binding of a local name. |
| `setGlobal : String → Expr → Stmt` | Write a module-level binding directly. Module-scope assignment, including `def` and `class`, lowers to this. |
| `declGlobal : String → Stmt` | `global x` — records a marker in `Env` that subsequent `assign`s to `x` consult. |
| `hole : String → Stmt` | An unmapped statement, tagged with the originating CPG node label. |

`Func` is a name, parameter list and body; `Program` is a list of `Func` plus the
`Dialect` the transpiler recorded. `Func.holes`, `Func.size`, `Func.total`,
`Program.verifiableCore` are the folds the ledger is computed from. `Func.total` inspects
only the AST, which is why static hole-freedom is an upper bound rather than a guarantee
(`docs/trust-model.md`).

## 5. Evaluation: four outcomes, not two

```lean
inductive EResult | val : Val → EResult | exn : Val → EResult
                  | hole : String → EResult | outOfFuel : EResult
```

`Ctl`, the statement-level outcome, adds `normal`, `ret`, `brk`, `cont` for control flow
and carries the same `exn` / `hole` / `outOfFuel`.

The two extra outcomes are both statements about ignorance, and they mean different
things:

* `val v` — the program has this behaviour.
* `exn v` — the program has this behaviour, and the behaviour is an exception. Raising is
  a specifiable outcome: "divides by zero raises `ZeroDivisionError`" is a specification,
  not a gap.
* `hole l` — *this was not translated*, or the interpreter reached a construct it cannot
  model. The program may have any behaviour here. No theorem may quantify over it.
* `outOfFuel` — *evaluation did not run long enough*. Says nothing about whether the
  program terminates.

Collapsing `hole` into an exception would make untranslated code look like specified
behaviour. Collapsing `outOfFuel` into a value would let a specification be satisfied by a
computation that never finished. They are therefore constructors rather than error
strings, and `Autoform/Refine.lean`'s `Outcome` type has **neither** — a refinement
statement is unsatisfiable by a function that holes or diverges (`refines_not_hole`,
`refines_terminates`).

The interpreter is **fuel-indexed and structurally recursive on the fuel**, so Lean accepts
it as total: no `partial`, no `unsafe`, no `sorry`. Fuel decrements at every recursive
step, so fuel is a bound on *evaluation depth*, not on execution steps; refinement
theorems therefore quantify `∀ fuel ≥ N` rather than picking one.

## 6. Dialects

```lean
inductive Dialect | python | cLike
```

Every program carries the dialect the transpiler inferred (`render_lean.py` infers it from
the file extension). Arithmetic and string semantics are parameterized by it.

This was not designed in. The differential harness's first run reported:

```
DIVERGENCE fmod(6, -9): cpython=-3 lean=6
```

Python floors integer division and modulo; C and Java truncate toward zero. The semantics
had picked one, which made it right for one language and wrong for every other. Patching
the operator is not sufficient: a universal core language must be parameterized by the
dialects it unifies, and the transpiler must record which one produced each program —
otherwise the proofs are about the wrong `eval`, and no amount of proving would surface
it.

The general rule: every place Core merges constructs that *look* alike across languages —
string mutability, integer width and overflow, evaluation order, name resolution,
equality — is a latent dialect parameter. Assume there are more, and let the oracles find
them.

The dialect currently controls:

* `Dialect.idiv`/`imod` — floored vs truncated division and remainder.
* `Dialect.toNumConfig` — the `NumConfig` from `Numeric.lean`: Python gets unbounded
  integers, `.cLike` gets 32-bit two's complement. (Which C policy is selected —
  `c32` surfacing undefined behaviour, or `c32Wrapv` matching what `cc` actually does — is
  a recorded choice, not a default: see §8 and `Numeric.lean`.)
* String operators: under `.python`, `+` concatenates and `<`/`>`/`==` compare contents;
  under `.cLike`, a `char*` is an address, so all three are holes rather than the Python
  answer applied to a C program.
* `Stdlib` — Python only. Under `.cLike` every builtin and method returns `none`, because
  answering a C program with Python's builtins is the original modulo bug again.

## 7. Numeric outcomes

`Numeric.lean`'s `NumResult` applies the same discipline one level down:

| Outcome | Meaning |
|---|---|
| `ok v` | A defined result. |
| `divZero` | Division or remainder by zero → `ZeroDivisionError`. |
| `trap r` | The language *defines* this as a runtime fault (Go's `INT_MIN / -1`) → an exception. |
| `ub r` | The language does not define this at all → **`Expr.hole "ub:<reason>"`**. |

C's signed overflow, `INT_MIN / -1` and shifts past the width have no correct answer; the
program's meaning depends on the compiler. Returning a number there would be the same
class of error as the original modulo bug, and harder to detect. Mapping `ub` to a hole
keeps undefined behaviour out of proofs entirely: a program that relies on UB cannot be
shown to do anything at that point.

## 8. The hole taxonomy

A hole is an untranslatable or unmodellable construct, labelled with what defeated the
translation. Labels come from two places:

* **Static holes** are emitted by `cartographer/export_ast.sc`. They are visible in
  `ast-<Module>.json` and are what the ledger's holes-by-cause table counts.
* **Runtime holes** are produced by the interpreter and are *invisible to static analysis*.
  A statically hole-free function can still hole on some input; that is the "dynamic-hole
  risk" figure, and it is the execution oracle's business, not the type system's.

The current static distribution is not a number in this document. Run:

```sh
python3 - <<'EOF'
import json, collections
c = collections.Counter()
def walk(x):
    if isinstance(x, dict):
        if x.get('k') == 'hole': c[x.get('label')] += 1
        for v in x.values(): walk(v)
    elif isinstance(x, list):
        for v in x: walk(v)
walk(json.load(open('ast-Cachetools.json')))
print(c.most_common()); print('total', sum(c.values()))
EOF
```

or read `holesByLabel` in `ledger-<Module>.json`, which the pipeline regenerates.

### Static labels (transpiler)

| Label family | Meaning | Status |
|---|---|---|
| `effect:kernel-sync:<operation>` | Lock, RCU, interrupt or preemption operation whose effects are not modeled. Argument evaluation and flag writes must not silently disappear. | Explicit unsupported effect. |
| ~~`op:starredUnpack`~~ | `*args` / `**kwargs` splicing. **Closed** (STRATEGY.md §35): `Expr.starred` / `Expr.kwargE` / `Expr.dstarred` and `Func.vararg` / `Func.kwarg` express it. The label no longer occurs. | Implemented. What remains is narrower and separately named: `op:starred-outside-call`, `call:<f>:keyword-to-builtin`. |
| `op:<name>` | An unmapped `<operator>.*` call. The generic `op:` bucket is where new operator work shows up. (`floorDiv` used to live here and is now mapped to `/`, because the dialect already makes `/` floor under `.python` — check `export_ast.sc`'s operator table before assuming an operator is missing.) | Not yet implemented (per operator). |
| `op:delete-index`, `op:delete-slice`, `op:delete-field`, `op:delete-shape` | `del d[k]`, slice deletion, attribute deletion. | Blocked on boxed containers (index/slice); the rest not yet implemented. |
| `op:dictLiteral-nonempty`, `op:stringExpressionList`, `op:fieldAccess-shape` | CPG node shapes the exporter does not recognise. | Not yet implemented. |
| `op:raise-bare` | A bare `raise` re-raising the in-flight exception; Core has no ambient current-exception. | Not yet implemented. |
| `op:raise-cause` | An explicit Python exception cause. | Cause evaluation and exception chaining remain unsupported. |
| `op:raise-source-metadata`, `op:raise-shape`, `op:raise-constructor-shape` | Python raise metadata or operand shape cannot be recovered faithfully. | Refuses to treat an arbitrary value as a valid exception. |
| `raise:ambiguous-exception-value` | A dynamically raised value is a string naming a represented exception class. | Core cannot distinguish that string from an exception instance. |
| `raise:unmodelled-object`, `raise:unmodelled-callable` | A dynamically raised object or callable cannot be classified. | Requires exception-instance or class semantics. |
| `exception:<class>:details-iterator`, `exception:<class>:unmodelled-class` | An exception constructor needs unsupported iteration or class semantics. | Refuses to guess the constructor outcome. |
| `raise:wrong-dialect`, `exception:wrong-dialect`, `exception:argument-shape` | Python exception intrinsics have an incompatible dialect or argument encoding. | Source lowering must supply Python and a tuple of evaluated constructor arguments. |
| `control:TRY-finally-escaping` | Historical label from before `tryFinally` lowering. | Returns, exceptions, breaks and continues now carry their local state through finalizers. |
| `control:TRY-source-metadata`, `control:TRY-handler-shape` | Original Python syntax is unavailable, cannot be parsed, or does not match the CPG's handler structure. | The exporter recovers headers with Python's parser because the CPG omits them. Missing metadata cannot become a catch-all. |
| `control:TRY-handler-type`, `control:TRY-handler-shadowed` | A handler names a type that is not a plain name (`socket.error`, `self.Error`), a name that is neither a builtin exception nor one of the program's own exception classes, or a builtin whose name is shadowed. | Builtin and corpus exception classes both dispatch (reference §8.4.1, closed over both hierarchies; `docs/languages.md` §16.C); attribute paths and aliases Core cannot see remain dynamic. |
| `control:TRY-handler-binding` | `except E as e` where `e` flows somewhere the exception's class name cannot stand in for the object (`return e`, `x = e`, `f(e)`). | The binding itself translates -- re-raise, `isinstance`, constructor arguments, and `e.args`/`str(e)` as `exception:payload:*` holes (`docs/languages.md` §16.C); the payload is not modelled: an exception is its class name. |
| `control:TRY-exception-group`, `control:TRY-handler-language` | Python exception groups or a handler in another source language. | Requires the corresponding language's dispatch semantics. |
| `control:TRY-else-without-except`, `control:TRY-multiFinally`, `control:TRY-shape` | Invalid or unrecognized handler/finalizer structure. | Explicit unsupported frontend shape. `control:TRY-multiCatch` is historical: ordered builtin handlers and tuples now lower to a dispatch chain. |
| `control:WHILE-iterator` | A desugared iterator loop the exporter could not reconstruct into `forIn`. | Not yet implemented. |
| `control:DO:condition-shape` | A do-while node without one identifiable condition and body. | Refuses ambiguous frontend structure instead of guessing child order. |
| `scope:nonlocal-write` | A write to an enclosing function's binding. Capture is by value, so a closure cannot mutate its enclosing frame. | **Permanent by design** until `Env` becomes shared mutable cells — see below. |
| `scope:class-closure` | A class defined inside a function whose methods read the enclosing scope, where `classClosure` does not apply. | Being closed; check the current AST. |
| `assign:arity`, `assign:lhs:<shape>`, `assign:aug-impure-target`, `assign:aug-impure-receiver` | Multiple assignment targets, assignment to a shape Core has no statement for, and augmented assignment whose target or receiver would have to be evaluated twice. | Mostly not yet implemented; the "impure" ones are a correctness refusal, not a gap. |
| `call:no-callee-name` | A call whose callee the CPG left unnamed and that is not itself a call. | `call:computed-callee` is retired: a callee that is itself a call (`f(x)(y)`, `d["k"](3)`) is `Expr.callValue`, which applies what the callee evaluates to and holes `call:value:not-callable` at run time on anything that is not a function, closure or boxed function object. |
| `call:effect-after-starred` | A starred argument followed by an argument with lifted assignments or increments. Saving the iterable would not preserve the timing of its expansion. | Explicit unsupported evaluation order. |
| `import:module-value`, `import:unresolved`, `import:absent:external`, `import:absent:prefix-in-cpg`, `import:absent:relative` | A module used as a value, or an import the CPG could not resolve. The `absent:` labels split the second case by *why*: the module is external to the CPG, a proper prefix of its path is in the CPG (so more resolver work could reach it), or it is a relative import whose target is missing. | Permanent for genuinely external modules; that is the boundary the assurance case declares. `absent:prefix-in-cpg` is the part that is not permanent. |
| `lit:float`, `lit:unquoted` | A float literal unsupported by the source exporter and a literal it could not decode. | Core has float values; source-literal translation still needs coverage. |
| `expr:BLOCK`, `expr:BLOCK-impure`, `expr:BLOCK-prelude`, `expr:empty-block`, `expr:genExp`, `expr:setComp`, `expr:comprehension-position`, `expr:<label>` | Statement-expressions. List/dict comprehensions lower (languages §10.6); `expr:genExp` remains a legacy refusal in positions that cannot carry a prelude. Recognized generator expressions compile to suspended frames; `setComp` has no Core set value; `comprehension-position` has no prelude slot. | Mixed. |
| `genexpr:source-metadata`, `genexpr:outer-loop-shape`, `genexpr:yield-shape`, `genexpr:free-variable-cells`, `genexpr:async` | Missing or ambiguous source scope, an unrecognized frontend lowering, captured shared cells or asynchronous iteration. | Explicit generator-expression gaps. |
| `cstr:pointer-arith`, `cstr:address-compare`, `cstr:address-equality` | C string operations that are pointer operations, refused rather than given the Python answer. | **Permanent by design** until Core models addresses. |
| `stmt:<label>`, `stmt:UNKNOWN:<...>` | A CPG statement node with no mapping. The `UNKNOWN` bucket is where new front-end shapes appear. | Not yet implemented. |

### Runtime labels (interpreter)

| Label | Raised when |
|---|---|
| `call:<name>` | The callee resolves neither in the program, nor as a value in scope, nor in the modelled stdlib. In the AST a call to an untranslated function is indistinguishable from a call to a translated one, which is why the ledger reports call-closure separately from hole-freedom. |
| `call:python-defaults` | Default storage and definition-time evaluation remain unsupported. The exporter inserts a hole before the body, including calls which supply every argument. Recovered signatures without defaults support required, positional-only and keyword-only binding. Historical ASTs can still contain `call:python-positional-only` and `call:python-keyword-only` holes; re-export to recover their signatures. |
| `call:python-signature-shape` | Source parameter names disagree with the exported CPG parameter shape. The exporter refuses to guess a signature. Legacy models without `pythonSignature` retain historical binding behavior and need re-export before claiming source call fidelity. |
| `call:python-receiver-signature` | A method lacks an ordinary first positional `self` (`def f()`, `def f(*, self)`, `def f(*self)`, `def f(receiver, a)`) or has decorators whose descriptor binding is not modeled. A receiver followed by collectors (`def f(self, *args, **kwargs)`) is NOT a gap any more: the stripped receiver's name travels as `pythonSignature.receiverName` and `kwargsRejected` refuses a `self=` keyword that would otherwise vanish into `**kwargs`. Placeholder argument collectors ensure the explicit gap is reached instead of producing an incorrect arity exception. They do not claim that the source method accepts arbitrary arguments. A positional-only `self` can still be modeled with `**kwargs`. |
| `call:python-decorator-binding` | A decorated function can be replaced by a callable with a different body or signature. Static calls cannot safely use the original declaration; calls remain explicit gaps before argument-binding rejection. |
| `call:python-private-parameters` | Parameters with private names inside a class scope require Python name mangling, including in nested functions. Their current source/CPG signature mapping is not faithful, so calls remain explicit gaps. |
| `function:python-default-evaluation` | Creating a Python function with defaults. Default expressions execute at definition time and can raise or retain mutable state; skipping them would change even callers which never invoke the function. |
| `call:python-signature-metadata`, `function:python-signature-metadata` | The source signature is unavailable or cannot be matched to its CPG method. Missing metadata cannot imply that the calling convention is supported. |
| `entry:<name>` | `runFunc`/`runMain` could not resolve the requested entry point. |
| `field:<f>:non-object`, `setField:<f>:non-object` | Attribute read/write on a non-reference. |
| `field:runtime-method`, `field:method-unresolved` | Taking an unsupported synthetic method as a value, or a method declaration whose body cannot be resolved. Ordinary source method values preserve their bound receiver. |
| `mcall:<Cls>.<m>` | No such method on the receiver's class. |
| `mcall:<m>:non-object` | Method call on a value the modelled stdlib does not cover. |
| `mcall:<m>:unboxed-container` | A *mutating* container method. Honouring it would update a temporary, because the CPG has already desugared `self.d.pop(k)` into `t = self.d; t.pop(k)`. |
| `mcall:dangling-ref` | The receiver's ref is not in the heap. |
| `index:unsupported` | Subscript of something that is not a list, tuple or dict. |
| `in:non-container`, `in:non-str-in-str` | Membership on a value that cannot be searched — including an instance whose class defines no `__contains__`. |
| `forIn:non-iterable` | Iterating a non-iterable. |
| `iterator:dict-keys-changed` | A dictionary's key layout changed without changing its size; CPython slot traversal is not represented. Value replacement is supported. |
| `iterator:sentinel-identity` | Callable/sentinel iteration needs identity that Core cannot decide and that can affect equality, such as two unboxed NaNs. |
| `iterator:exception-hierarchy` | A sequence or callable iterator caught a user exception whose ancestry its synthetic handler cannot determine. |
| `iterator:result-protocol` | An `__iter__` result has no translated `__next__`, but inherited or metaclass behavior is not represented well enough to prove it absent. Known non-iterator builtin results raise `TypeError`. |
| `iterator:length-hint`, `iterator:sum-type` | A consumer needs an observable custom length hint or accumulation outside the exact integer model. |
| `iterator:invalid-index`, `iterator:source-kind-changed`, `iterator:dangling-reference` | A malformed internal iterator state. Source-created iterators keep these fields private. |
| `setIndex:immutable-containers` | *Any* `e[i] = v`. Containers are values, so a write cannot be observed by anything else holding the container. |
| `binop:<op>`, `unop:<op>` | An operator name with no case, or with no case for those operand types (e.g. arithmetic on a string). |
| `numeric:unknown-type:<op>` | Joern did not supply enough type information to choose an integer width and signedness. |
| `numeric:operand:<op>` | A typed integer operator received a value outside its model, including JS string/object coercion. |
| `numeric:unsupported-js-op:<op>` | A numeric tag requests an operation outside the JS Number bitwise subset. |
| `ub:<reason>` | The configured integer arithmetic says the source language does not define this operation. |
| `str:pointer-arithmetic-not-modelled`, `str:pointer-compare-not-modelled`, `str:pointer-equality-not-modelled` | A C string operation under `.cLike`. |
| `call:stray-control-flow` | A `brk`/`cont` escaped a function body — a transpiler bug if it appears. |
| `initializers:outOfFuel` | Module initializers did not finish within the fuel budget. |

New Python exports carry lexical method classification in `pythonSignature.isMethod`.
Nested functions keep their ordinary parameters even when a class has the same name
as their enclosing function. Core uses this metadata for unbound method calls;
legacy models without it retain the historical name-based heuristic and must be
re-exported before claiming faithful receiver binding.

### Permanent by design vs not yet implemented

The distinction tells you whether a hole is work or a boundary.

**Boundaries** (closing them means changing the design):

* `scope:nonlocal-write` and global *rebinding*. Making these work requires every scope to
  be a heap frame and `Env` to be references — a large refactor of the interpreter and a
  re-repair of the entire refinement layer. Implementing writes by copying values back
  would appear to work on simple cases and be silently wrong on aliased ones. Reads across
  scopes work and are correct; writes are a hole.
* `cstr:*` and `str:pointer-*`. Core has one `Val.str` for Python strings and C `char*`.
  Rather than model addresses, the operations that differ are refused.
* `op:starred-outside-call`. A starred form outside an argument list (`a, *b = xs`) is
  a *destructuring* pattern, not a call, and Core has no pattern binding. The calling
  convention (§35) covers the call side only.
* `import:*` for genuinely external modules — the effect boundary itself, which the SACM
  case declares as an assumption.
* `ub:*`. The semantics refusing to commit where the source language does not define an
  answer.

**Work** (a known design would close them):

* `setIndex:immutable-containers`, `mcall:*:unboxed-container`, `op:delete-index/slice` —
  all one feature: boxed mutable containers. See `docs/boxed-containers.md`.
* `lit:float` and remaining float skips in the differential oracle — source-literal
  translation and runtime value encoding beyond the supported cases.
* `control:TRY-*` beyond the translated shapes — a richer control-flow encoding.
* `call:<name>` for stdlib callees — more of `Stdlib.lean`. This is the largest single
  lever on the verifiable core, because a function is only as analysable as its callees.
* The `expr:`, `stmt:`, `op:` generic buckets — ordinary exporter work.

The governing rule: **an honest hole with a precise label beats a wrong translation.** A
hole is counted, declared, and blocks proof at exactly the right point. A wrong
translation is invisible until an oracle happens to look.
