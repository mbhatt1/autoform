# The Core language

`Autoform.Core` is the deep-embedded universal imperative language that every translated
codebase is mapped onto. It is the heart of the system: coverage, conformance, refinement
and the whole trust ledger are statements about terms of these types and about the
interpreter that runs them.

Source of truth: `Autoform/Lang/Core/Syntax.lean` and `Autoform/Lang/Core/Semantics.lean`.
Where this document and the source disagree, the source is right and this document is a
bug. Nothing here restates a number; the shapes are stable, the counts are not.

Core is shaped to match **Joern's CPG node vocabulary**, not any one language's grammar.
That is the whole reason one semantics can cover C, C++, Java, JavaScript, Python and
Kotlin: the front ends have already normalized to a common vocabulary, so Core only has to
be faithful to *that*.

---

## 1. Values (`Val`)

| Constructor | Meaning |
|---|---|
| `int : Int → Val` | An integer. Width and overflow are **not** properties of the value — they belong to `NumConfig`, selected by the dialect. A `Val.int` is always the mathematical integer that the configured arithmetic produced. |
| `str : String → Val` | A string *or* a C `char*`. Deliberately one constructor: see §7, where the operators are dialect-split instead. |
| `bool : Bool → Val` | A boolean. |
| `unit : Val` | The absence of a value: an unbound name, a function that fell off the end, an absent field. |
| `list : List Val → Val` | A list. **Immutable** — Core has no boxed containers, which is why `Stmt.setIndex` is a hole. |
| `tuple : List Val → Val` | A tuple. Same immutability. |
| `dict : List (Val × Val) → Val` | An association list, *not* a hash map. Key order is observable in real languages and differs between them, so imposing one language's iteration order would be an invented answer. |
| `ref : Ref → Val` | A reference to a heap object. Reference identity is what `is` compares. |
| `fn : String → Val` | A function, method or class used as a value (CPG `METHOD_REF` / `TYPE_REF`). |
| `clos : String → List (String × Val) → Val` | A closure: a function name plus the bindings it captured. Capture is **by value**. |
| `clsClos : String → List (String × Val) → Val` | A *class* value that captured an enclosing scope. Distinct from `clos` because a class is not a function: its methods, not it, read the captured bindings. |
| `bobj : String → Val → Val` | An instance of a class whose **base is a builtin type** (`class X(tuple)`, `(list)`, `(dict)`, `(str)`): the class name plus the underlying builtin value. It compares, iterates, indexes and tests membership as the builtin does, which is what makes `hashkey(0) == (0,)` true as it is in CPython. It has **no mutable attributes** — a `bobj` is a value, not a heap object — so `e.f` on one is a hole. Which classes get one is recorded per program in `Program.builtinBases`; a class the exporter did not record stays an opaque `ref`. See `Autoform/BuiltinBase.lean`. |

Two derived functions matter:

* `Val.truthy` — the permissive truthiness shared by most dynamic languages (empty
  containers, `0`, `""` and `unit` are false; references and callables are true).
* `Val.iterable` — what a value iterates over, if anything. `none` for everything that is
  not a list, tuple or dict (or a `bobj` over one); `forIn` over anything else is a hole.
* `Val.unbuiltin` — strips one layer of builtin-base wrapping. Deliberately
  non-recursive, so the functions that use it stay plain matchers that reduce by `rfl`.

`Val.beq` is hand-written structural equality (the nested `List`/`Prod` occurrences block
`deriving DecidableEq`). Closures and class closures compare by *name only*, ignoring
captured environments.

A `bobj` compares by its **contents, ignoring the class**, and compares equal to the plain
builtin: CPython's `tuple.__eq__` does the same, and `A((0,)) == B((0,))` is `True` there
for two distinct subclasses of `tuple`. That is only sound because `Expr.alloc` *refuses*
to build a `bobj` for a class that defines its own `__eq__` (or its own `__init__`),
emitting `alloc:builtin-base:<cls>:own-__eq__` instead — `Val.beq` has no dunder dispatch,
so honouring such a class would mean silently ignoring the override.

There is deliberately **no float constructor**. `Autoform/Lang/Core/Float.lean` develops a
full IEEE-754 model as an explicit bit pattern, but at the time of writing it is not wired
into `Val`; floats therefore still surface as holes and as skipped differential cases.

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
* **Reads of absent things are `unit`**, not an error: `Env.get` on an unbound name,
  `Heap.getField` on an absent field, `Heap.get` on a dangling ref. This is Python-shaped
  and is one of the places where a wrong answer is possible; the differential oracle is
  what catches it (private name mangling was exactly this bug).
* **Field lookup order** is the object's own fields, then the bindings its class captured,
  then `unit`.
* **Globals live on the heap, not in `Env`.** Module-level bindings must be mutable and
  must outlive any single call, so they occupy a distinguished object (`cls = "<globals>"`)
  at `Ctx.globals`. `runMain` allocates it first, so it is ref 0, and any harness building
  its own heap must allocate fresh objects from `heap.length` onward.
* **The heap is threaded explicitly** through `evalExpr`/`execStmt` rather than hidden in a
  monad. That is a deliberate cost: it keeps the fuel recursion visibly structural, so Lean
  accepts the interpreter as total without `partial`.
* **`Ctx.resolve` falls back from exact name to *unique* suffix match**, because Joern emits
  fully-qualified names (`pkg/mod.py:<module>.Cls.meth`) while call sites carry short ones.
  This is a heuristic, and it is written so that an *ambiguous* match resolves to a hole
  rather than to a guess. `Ctx.resolveMethod` prefers `Cls.meth` and falls back to any
  `.meth`.

## 3. Expressions (`Expr`)

| Constructor | Meaning |
|---|---|
| `lit : Lit → Expr` | An `int` / `str` / `bool` / `unit` literal. |
| `name : String → Expr` | Variable read. Resolution order: local `Env`, then the globals frame, then the function table (yielding `Val.fn`), then `unit`. The function-table fallback is what makes higher-order code translatable instead of holed. |
| `binop : String → Expr → Expr → Expr` | Binary operator by name. `&&`/`\|\|` short-circuit (§5); everything else evaluates left then right. |
| `unop : String → Expr → Expr` | Unary operator by name (`-`, `!`). |
| `call : String → List Expr → Expr` | Call by name. Tries `Ctx.resolve`, then a `Val.fn`/`Val.clos` held in a variable, then the modelled stdlib, then a `call:<name>` hole. The stdlib is consulted **last** so a user function of the same name always wins. |
| `index : Expr → Expr → Expr` | Subscript. Out-of-range list/tuple index raises `IndexError`; a missing dict key raises `KeyError`; anything else is `index:unsupported`. |
| `field : Expr → String → Expr` | Attribute read. A non-reference receiver is `field:<f>:non-object`. |
| `mcall : Expr → String → List Expr → Expr` | Method call, dispatched on the receiver's class. A non-object receiver falls through to the modelled stdlib's container methods; a *mutating* container method is `mcall:<m>:unboxed-container` because writing back through the receiver expression would update a temporary. |
| `alloc : String → List Expr → Expr` | Construction. Allocates a fresh object, copies in any bindings the class captured, and runs `__init__` if one resolves. |
| `fnref : String → Expr` | A function, method or class as a value. |
| `closure : String → Expr` | A function value that captures the current `Env` by value: decorators, factories, nested functions reading outer variables. |
| `classClosure : String → Expr` | A class value that captures the current `Env`; instances carry those bindings so their methods can read the enclosing scope. |
| `listE` / `tupleE` / `dictE` | Container literals. |
| `cond : Expr → Expr → Expr → Expr` | Conditional expression; only the taken branch is evaluated. |
| `isOp : Bool → Expr → Expr → Expr` | Identity. Reference identity for `.ref`, structural for immediates. The `Bool` means negated (`is not`). |
| `inOp : Bool → Expr → Expr → Expr` | Membership over lists, tuples, dict keys, and substrings. The `Bool` means negated (`not in`). |
| `hole : String → Expr` | An unmapped expression, tagged with the CPG node label that produced it. |

## 4. Statements (`Stmt`)

| Constructor | Meaning |
|---|---|
| `skip` | No-op. |
| `expr : Expr → Stmt` | Evaluate for effect; discard the value (but not exceptions or holes). |
| `assign : String → Expr → Stmt` | Local binding — unless a `declGlobal` marker for that name is in scope, in which case it writes the globals frame. |
| `setField : Expr → String → Expr → Stmt` | `e.f = v`. Non-object receiver: `setField:<f>:non-object`. |
| `setIndex : Expr → Expr → Expr → Stmt` | `e[i] = v`. **Always** the hole `setIndex:immutable-containers` — see §8. |
| `seq : Stmt → Stmt → Stmt` | Sequencing. Only a `normal` outcome continues. |
| `ifte` / `loop` | Conditional and `while`. |
| `forIn : String → Expr → Stmt → Stmt` | Iterate over an already-computed sequence (`Val.iterable`); a non-iterable is `forIn:non-iterable`. Note the CPG for Python has no `FOR` node — the front end desugars every `for` and comprehension into an iterator protocol plus a `WHILE`, and the exporter reconstructs `forIn` from that shape. |
| `ret` / `brk` / `cont` | Return, break, continue — each its own `Ctl` outcome. |
| `tryCatch : Stmt → String → Stmt → Stmt` | `try/except as x`. Catches **exceptions only**: `ret`/`brk`/`cont` pass straight through, or every `try` containing a `return` would break. |
| `tryFinally : Stmt → Stmt → Stmt` | The finalizer runs on *every* exit path, and an abnormal exit from the finalizer discards the body's pending outcome — Python's rule, so `try: return 1 finally: return 2` returns 2. |
| `raise : Expr → Stmt` | Raise the evaluated value as an exception. |
| `del : String → Stmt` | Remove every binding of a local name. |
| `setGlobal : String → Expr → Stmt` | Write a module-level binding directly. Module-scope assignment, including `def` and `class`, lowers to this. |
| `declGlobal : String → Stmt` | `global x` — records a marker in `Env` that subsequent `assign`s to `x` consult. |
| `hole : String → Stmt` | An unmapped statement, tagged with the originating CPG node label. |

`Func` is a name, parameter list and body; `Program` is a list of `Func` plus the
`Dialect` the transpiler recorded. `Func.holes`, `Func.size`, `Func.total`,
`Program.verifiableCore` are the folds the ledger is computed from — and note that
`Func.total` inspects only the AST, which is why static hole-freedom is an upper bound
rather than a guarantee (`docs/trust-model.md`).

## 5. Evaluation: four outcomes, not two

```lean
inductive EResult | val : Val → EResult | exn : Val → EResult
                  | hole : String → EResult | outOfFuel : EResult
```

`Ctl`, the statement-level outcome, adds `normal`, `ret`, `brk`, `cont` for control flow
and carries the same `exn` / `hole` / `outOfFuel`.

The four-way split is the single most important design decision in the interpreter,
because the two extra outcomes are both statements about **our ignorance**, and they mean
different things:

* `val v` — the program has this behaviour.
* `exn v` — the program has this behaviour, and the behaviour is an exception. Raising is
  a real, specifiable outcome: "divides by zero raises `ZeroDivisionError`" is a
  specification, not a gap.
* `hole l` — *we did not translate this*, or the interpreter reached a construct it cannot
  model. The program may have any behaviour here. No theorem may quantify over it.
* `outOfFuel` — *we did not run long enough*. Says nothing about whether the program
  terminates.

Collapsing `hole` into an exception would make untranslated code look like specified
behaviour. Collapsing `outOfFuel` into a value would let a specification be satisfied by a
computation that never finished. Both are the failure this project exists to prevent, so
they are constructors rather than error strings, and `Autoform/Refine.lean`'s `Outcome`
type deliberately has **neither** — a refinement statement is therefore unsatisfiable by a
function that holes or diverges (`refines_not_hole`, `refines_terminates`).

The interpreter is **fuel-indexed and structurally recursive on the fuel**, so Lean accepts
it as total: no `partial`, no `unsafe`, no `sorry`. Fuel decrements at every recursive
step, which means fuel is a bound on *evaluation depth*, not on execution steps; refinement
theorems therefore quantify `∀ fuel ≥ N` rather than picking one.

## 6. Dialects

```lean
inductive Dialect | python | cLike
```

Every program carries the dialect the transpiler inferred (`render_lean.py` infers it from
the file extension). Arithmetic and string semantics are parameterized by it.

This was **not** designed in. The differential harness's first run reported:

```
DIVERGENCE fmod(6, -9): cpython=-3 lean=6
```

Python floors integer division and modulo; C and Java truncate toward zero. The semantics
had silently picked one, which meant it was right for one language and quietly wrong for
every other. The tempting fix is to patch the operator. The correct fix is structural: a
universal core language **must** be parameterized by the dialects it unifies, and the
transpiler **must** record which one produced each program — otherwise the proofs are all
about the wrong `eval`, and no amount of proving would ever surface it.

The general rule, worth applying to anything added later: every place Core merges
constructs that *look* alike across languages — string mutability, integer width and
overflow, evaluation order, name resolution, equality — is a latent dialect parameter.
Assume there are more, and let the oracles find them.

Concretely, the dialect currently controls:

* `Dialect.idiv`/`imod` — floored vs truncated division and remainder.
* `Dialect.toNumConfig` — the `NumConfig` from `Numeric.lean`: Python gets unbounded
  integers, `.cLike` gets 32-bit two's complement. (Which C policy is selected —
  `c32` surfacing undefined behaviour, or `c32Wrapv` matching what `cc` actually does — is
  a recorded choice, not a default: see §8 and `Numeric.lean`.)
* String operators: under `.python`, `+` concatenates and `<`/`>`/`==` compare contents;
  under `.cLike`, a `char*` is an address, so all three are holes rather than the Python
  answer applied to a C program.
* `Stdlib` — Python only. Under `.cLike` every builtin and method returns `none`, because
  answering a C program with Python's builtins is exactly the original modulo bug again.

## 7. Numeric outcomes

`Numeric.lean`'s `NumResult` mirrors the same discipline one level down:

| Outcome | Meaning |
|---|---|
| `ok v` | A defined result. |
| `divZero` | Division or remainder by zero → `ZeroDivisionError`. |
| `trap r` | The language *defines* this as a runtime fault (Go's `INT_MIN / -1`) → an exception. |
| `ub r` | The language does not define this at all → **`Expr.hole "ub:<reason>"`**. |

`ub` is the one that matters. C's signed overflow, `INT_MIN / -1` and shifts past the width
have no correct answer; the program's meaning depends on the compiler. Returning a number
there would be the same class of error as the original modulo bug, only harder to detect.
Mapping `ub` to a hole keeps undefined behaviour out of proofs entirely: a program that
relies on UB provably cannot be shown to do anything at that point.

## 8. The hole taxonomy

A hole is an untranslatable or unmodellable construct, labelled with what defeated the
translation. Labels come from two places, and the distinction is worth keeping straight:

* **Static holes** are emitted by `cartographer/export_ast.sc`. They are visible in
  `ast-<Module>.json` and are what the ledger's holes-by-cause table counts.
* **Runtime holes** are produced by the interpreter and are *invisible to static analysis*.
  A statically hole-free function can still hole on some input; that is the "dynamic-hole
  risk" figure, and it is the execution oracle's business, not the type system's.

To see the current static distribution, do not read a number out of a document — run:

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
| `op:starredUnpack` | `*args` / `**kwargs` splicing. Has no Core representation — splicing changes arity, which cannot be expressed by a fixed parameter list. | **Permanent** without variadic functions in Core. |
| `op:<name>` | An unmapped `<operator>.*` call. The generic `op:` bucket is where new operator work shows up. (`floorDiv` used to live here and is now mapped to `/`, because the dialect already makes `/` floor under `.python` — check `export_ast.sc`'s operator table before assuming an operator is missing.) | Not yet implemented (per operator). |
| `op:delete-index`, `op:delete-slice`, `op:delete-field`, `op:delete-shape` | `del d[k]`, slice deletion, attribute deletion. | Blocked on boxed containers (index/slice); the rest not yet implemented. |
| `op:dictLiteral-nonempty`, `op:stringExpressionList`, `op:fieldAccess-shape` | CPG node shapes the exporter does not recognise. | Not yet implemented. |
| `op:raise-bare` | A bare `raise` re-raising the in-flight exception; Core has no ambient current-exception. | Not yet implemented. |
| `control:TRY-finally-escaping` | `try/finally` whose body can `return`/`break`. The non-escaping case *is* translated; when control escapes, `ret` would bypass the trailing finalizer. | Design-limited; needs a richer `Ctl` interaction than one `tryCatch` can express. |
| `control:TRY-else-without-except`, `control:TRY-multiCatch`, `control:TRY-multiFinally`, `control:TRY-shape` | `try/except/else` (the `else` must run only when nothing was raised, *and* its own exceptions must not be caught), multiple `except` clauses (the CPG discards exception types), and unrecognised `try` shapes. | Partly permanent (the CPG loses the exception types), partly not yet implemented. |
| `control:WHILE-iterator` | A desugared iterator loop the exporter could not reconstruct into `forIn`. | Not yet implemented. |
| `scope:nonlocal-write` | A write to an enclosing function's binding. Capture is by value, so a closure cannot mutate its enclosing frame. | **Permanent by design** until `Env` becomes shared mutable cells — see below. |
| `scope:class-closure` | A class defined inside a function whose methods read the enclosing scope, where `classClosure` does not apply. | Being closed; check the current AST. |
| `assign:arity`, `assign:lhs:<shape>`, `assign:aug-impure-target`, `assign:aug-impure-receiver` | Multiple assignment targets, assignment to a shape Core has no statement for, and augmented assignment whose target or receiver would have to be evaluated twice. | Mostly not yet implemented; the "impure" ones are a correctness refusal, not a gap. |
| `call:computed-callee`, `call:no-callee-name` | A call whose callee is an expression rather than a name the CPG resolved. | Not yet implemented. |
| `import:module-value`, `import:unresolved` | A module used as a value, or an import the CPG could not resolve. | Permanent for genuinely external modules; that is the boundary the assurance case declares. |
| `lit:float`, `lit:unquoted` | A float literal (Core has no float value) and a literal the exporter could not decode. | `lit:float` is blocked on wiring `Float.lean` into `Val`. |
| `expr:BLOCK`, `expr:BLOCK-impure`, `expr:BLOCK-prelude`, `expr:empty-block`, `expr:genExp`, `expr:<label>` | Statement-expressions and generator expressions. `genExp` needs laziness Core does not have. | Mixed. |
| `cstr:pointer-arith`, `cstr:address-compare`, `cstr:address-equality` | C string operations that are pointer operations, refused rather than given the Python answer. | **Permanent by design** until Core models addresses. |
| `stmt:<label>`, `stmt:UNKNOWN:<...>` | A CPG statement node with no mapping. The `UNKNOWN` bucket is where new front-end shapes appear. | Not yet implemented. |

### Runtime labels (interpreter)

| Label | Raised when |
|---|---|
| `call:<name>` | The callee resolves neither in the program, nor as a value in scope, nor in the modelled stdlib. **This is the dangerous one**: in the AST a call to an untranslated function is indistinguishable from a call to a translated one, which is exactly why the ledger reports call-closure separately from hole-freedom. |
| `entry:<name>` | `runFunc`/`runMain` could not resolve the requested entry point. |
| `field:<f>:non-object`, `setField:<f>:non-object` | Attribute read/write on a non-reference. |
| `mcall:<Cls>.<m>` | No such method on the receiver's class. |
| `mcall:<m>:non-object` | Method call on a value the modelled stdlib does not cover. |
| `mcall:<m>:unboxed-container` | A *mutating* container method. Honouring it would update a temporary, because the CPG has already desugared `self.d.pop(k)` into `t = self.d; t.pop(k)`. |
| `mcall:dangling-ref` | The receiver's ref is not in the heap. |
| `index:unsupported` | Subscript of something that is not a list, tuple or dict. |
| `in:non-container`, `in:non-str-in-str` | Membership on a value that cannot be searched. |
| `forIn:non-iterable` | Iterating a non-iterable. |
| `setIndex:immutable-containers` | *Any* `e[i] = v`. Containers are values, so a write cannot be observed by anything else holding the container. |
| `binop:<op>`, `unop:<op>` | An operator name with no case, or with no case for those operand types (e.g. arithmetic on a string). |
| `ub:<reason>` | The configured integer arithmetic says the source language does not define this operation. |
| `str:pointer-arithmetic-not-modelled`, `str:pointer-compare-not-modelled`, `str:pointer-equality-not-modelled` | A C string operation under `.cLike`. |
| `call:stray-control-flow` | A `brk`/`cont` escaped a function body — a transpiler bug if it ever appears. |
| `initializers:outOfFuel` | Module initializers did not finish within the fuel budget. |

### Permanent by design vs not yet implemented

The distinction is not cosmetic — it is what tells you whether a hole is work or a
boundary.

**Boundaries** (closing them means changing the design, and the design is deliberate):

* `scope:nonlocal-write` and global *rebinding*. Making these work requires every scope to
  be a heap frame and `Env` to be references — a correct design, a large refactor of the
  interpreter, and a re-repair of the entire refinement layer. Implementing writes by
  copying values back would appear to work on simple cases and be silently wrong on
  aliased ones. Reads across scopes work and are correct; writes are a hole. That is the
  honest boundary.
* `cstr:*` and `str:pointer-*`. Core has one `Val.str` for Python strings and C `char*`.
  Rather than model addresses, the operations that differ are refused.
* `op:starredUnpack`. Variadic arity is not expressible against a fixed `params` list.
* `import:*` for genuinely external modules — this is the effect boundary itself, and the
  SACM case declares it as an assumption rather than pretending it away.
* `ub:*`. Not a gap at all: it is the semantics correctly refusing to commit where the
  source language does not define an answer.

**Work** (a known design would close them):

* `setIndex:immutable-containers`, `mcall:*:unboxed-container`, `op:delete-index/slice` —
  all one feature: boxed mutable containers. See `docs/boxed-containers.md`.
* `lit:float` and the float skips in the differential oracle — wiring `Float.lean` into
  `Val`.
* `control:TRY-*` beyond the translated shapes — a richer control-flow encoding.
* `call:<name>` for stdlib callees — more of `Stdlib.lean`. This is the largest single
  lever on the verifiable core, because a function is only as analysable as its callees.
* The `expr:`, `stmt:`, `op:` generic buckets — ordinary exporter work.

The rule that governs every one of these: **an honest hole with a precise label always
beats a wrong translation.** A hole is counted, declared, and blocks proof at exactly the
right point. A wrong translation is invisible until an oracle happens to look.
