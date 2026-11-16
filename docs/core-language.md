# The Core language

`Autoform.Core` is the deep-embedded universal imperative language that every translated
codebase is mapped onto. Coverage, conformance, refinement and the trust ledger are all
statements about terms of these types and about the interpreter that runs them.

Source of truth: `Autoform/Lang/Core/Syntax.lean` and `Autoform/Lang/Core/Semantics.lean`.
Where this document and the source disagree, the source is right and this document is a
bug. Nothing here restates a number; the shapes are stable, the counts are not.

Core is shaped to match **Joern's CPG node vocabulary**, not any one language's grammar.
That is why one semantics can cover C, C++, Java, Kotlin, Go, JavaScript, TypeScript and
Python (the extension table `DIALECT` in `cartographer/render_lean.py` is the list): the
front ends have already normalized to a common vocabulary, so Core only has to be faithful
to *that*.

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
| `iref : Ref → Sel → Val` | An *interior* pointer: a reference to a heap-boxed array or struct **plus** a position within it (`Sel.idx : Int → Sel` for an element, `Sel.fld : String → Sel` for a member). C's `&a[i]` / `&s.f` / `p + 1`. Kept distinct from `ref` because only an interior pointer has pointer arithmetic (`applyBinop`), and only on the `.idx` case: arithmetic on a `.fld` selector is the hole `iref:arith-on-field`, since C gives it no meaning. |
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

Python conditions, negation, Boolean operators, and truth conversion of comparison
results use `evalTruthWith`. It reads native container payloads and runs declared
`__bool__`/`__len__` methods through the ordinary fuel-bounded interpreter, carrying
heap changes and exceptions into the continuation. `any`/`all` use the same private
truth protocol. Unknown object protocols remain `truth:unresolved-protocol`; a length
requiring an unrepresented `__index__` protocol is `length:index-protocol`, and a
length above the portable signed 32-bit bound is `truth:length-platform`.

The Python renderer distinguishes a branch's truth test from a materialized Boolean
expression. It preserves a previously computed answer within one short-circuit
expression, including across lifted statement preludes and suspended frames. An
independent later test runs the protocol again. Auxiliary truth helpers are excluded
from the source-function population, and source operations remain in `analysisBody`.
Compiler-created temporary expressions can carry `pythonTruthCache`, an expression
that reads an internal state: `0` is untested, `1` is false, and `2` is true. The
exporter assigns it on every selected branch; generator lowering moves its binding
into the frame alongside other locals. The renderer consumes it only within the
original Boolean expression. Source-level variable reads do not inherit the cache.
The pure-expression refinement fragment excludes operations that may invoke a truth
method; branch and loop rules carry the truth test's resulting heap explicitly.

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
  `AttributeError` when recovered class metadata makes the hierarchy complete, and is the
  named gap `field:<attr>:unresolved-inheritance` on a legacy model that has no
  hierarchy to search (Language Reference §3.2.11/§3.3.2, `docs/languages.md` §16.A);
  under `.javascript` it is `undefined` = `unit` (ECMA-262 OrdinaryGet). The differential oracle
  is what settled the Python answer (private name mangling was the first bug it found
  here, a missing attribute answering `unit` the latest).
* **Field lookup order** (`Expr.field`) is the object's own fields, then the bindings its
  class captured, then a `@property` getter, then a class attribute; after that,
  `AttributeError` under `.python` with class metadata, a named gap under `.python`
  without it, and `unit` elsewhere. A stored class attribute holding a Python function
  (a decorated method's value) is a non-data descriptor: read through an instance it is a
  bound method (`<bound-method>.<function>`, the receiver passed first), read through the
  class it is the plain function, and a value that may define `__get__`/`__set__`/
  `__delete__` is `class-attribute:<attr>:descriptor-object` for reads and writes.
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
| `callValue : Expr → List Expr → Expr` | Call of a *computed* callee (`f(x)(y)`, `d["k"](3)`, `make()(v)`). `call` is by name; this applies whatever value the callee evaluates to — a function, a closure, a boxed function object — and holes `call:value:not-callable` on anything else. Arguments take the same three forms as `call`. |
| `alloc : String → List Expr → Expr` | Construction. Allocates a fresh object, copies in any bindings the class captured, and runs `__init__` if one resolves. |
| `fnref : String → Expr` | A function, method or class as a value. |
| `closure : String → Expr` | A function value that captures the current `Env` by value: decorators, factories, nested functions reading outer variables. |
| `classClosure : String → Expr` | A class value that captures the current `Env`; instances carry those bindings so their methods can read the enclosing scope. |
| `listE` / `tupleE` / `dictE` | Container literals. |
| `cond : Expr → Expr → Expr → Expr` | Conditional expression; only the taken branch is evaluated. |
| `isOp : Bool → Expr → Expr → Expr` | Identity. Reference identity for `.ref`, structural for immediates. The `Bool` means negated (`is not`). |
| `inOp : Bool → Expr → Expr → Expr` | Membership over lists, tuples, dict keys, and substrings; under `.python`, on an ordinary instance whose class defines `__contains__`, it IS `c.__contains__(x)` and `not in` negates that result's truthiness. The `Bool` means negated (`not in`). |
| `starred : Expr → Expr` | `*e` in an argument list: splice an iterable into the positional arguments; a non-iterable raises `TypeError`. Only an argument list evaluates it — anywhere else it is the hole `op:starred-outside-call`. |
| `kwargE : String → Expr → Expr` | `k = e` in an argument list: one keyword argument. Before this existed the exporter dropped such arguments silently. |
| `dstarred : Expr → Expr` | `**e` in an argument list: splice a `dict` into the keyword arguments; a non-`dict`, or a `dict` with non-string keys, raises `TypeError`. |
| `boxNew : Expr → Expr` | Unconditional, constructor-free allocation of a fresh single-field object (`cls := "<local>"`, field `v`) holding the argument, returning its `ref`. The primitive behind boxing an address-taken C local; `alloc` is wrong for it because `alloc` runs a named class's `__init__`. |
| `boxFields : List (Expr × Expr) → Expr` | `boxNew` generalised to N fields: allocates a fresh object from (key, initial value) pairs evaluated left to right. The per-function prologue for every C array or struct local — an array's elements become fields keyed by decimal-string index, a struct's members by name. Keys are `Expr`s (always string literals as emitted) so evaluation reuses `evalPairs` and its fuel proof; a non-string key is a hole. |
| `boxArray : Expr → Expr` | Allocation of a fresh object whose field count is a *runtime* value: evaluates the length once and builds fields `"0"`…`"n-1"`, each `.unit`. Exists because `boxFields`' list is syntax in the generated source, so a 512–8,192-element buffer blew the elaborator; this is what `malloc(n)` lowers to. |
| `irefIndex : Expr → Expr → Expr` | `&a[i]` on a boxed array: evaluates the receiver to `ref r` and the index to `i`, producing `iref r (.idx i)`. The address-of counterpart to `index`, which stays a whole-value read. |
| `irefField : Expr → String → Expr` | `&s.f` on a boxed struct: `iref r (.fld f)`. The address-of counterpart to `field`. |
| `derefIref : Expr → Expr` | `*p` where `p` evaluates to an interior pointer: delegates to the unchanged `Heap.getField h r sel.key`. |
| `strByte : Expr → Expr → Expr` | C's `*p` / `p[i]` on a `char*` walked as a byte cursor: the character at position `b` of string `a` **as an integer** (so `*z == '"'` and `*z - '0'` work), emitted only by the C-family exporter path because Python's `s[i]` returns a length-1 string from the same syntax. Reading at exactly the string's length yields `0` (the implicit terminator); any other out-of-range read is a hole. Indexes by codepoint, identical to bytes for ASCII. |
| `strFrom : Expr → Expr → Expr` | The substring of `a` from position `b` to its end — Python's `s[i:]`, and what a walked C cursor is worth when passed whole to another function. Clamped like `List.drop`: a start past the end is `""`; a negative start is a hole. |
| `slice : Expr → Expr → Expr → Expr → Expr` | `xs[lo:hi:st]` (`docs/boxed-containers.md` §9 item 3). An omitted bound is `.lit .unit`, because that is Python's own definition (`xs[:2]` *is* `xs[slice(None, 2, None)]`). Evaluates to a **new** container — a fresh boxed list, a `tuple`, or a `str` — with CPython's `slice.indices` normalisation and its `ValueError` on a zero step. |
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
| `setSlice : Expr → Expr → Expr → Expr → Expr → Stmt` | `xs[lo:hi:st] = v`, bounds as in `Expr.slice`. A unit step replaces the range with the iterable whatever its length (CPython's `xs[3:1] = [9]` inserts at 3); any other step is an *extended* assignment and demands equal lengths, else `ValueError`. Only a list payload is assignable; a tuple payload is `TypeError`. |
| `delSlice : Expr → Expr → Expr → Expr → Stmt` | `del xs[lo:hi:st]`: removes exactly the positions the slice denotes, for any step. |
| `setDerefIref : Expr → Expr → Stmt` | `*p = v` where `p` evaluates to an interior pointer (`Val.iref r sel`): delegates to the unchanged `Heap.setField h r sel.key v`. The write-side counterpart of `Expr.derefIref`. |
| `seq : Stmt → Stmt → Stmt` | Sequencing. Only a `normal` outcome continues. |
| `ifte` / `loop` | Conditional and `while`. |
| `breakBlock : Stmt → Stmt` | Absorbs a `brk` from its body **without** absorbing a `cont` — the one thing `loop`/`forIn` do not offer, since both catch `cont` by re-entering. A C `switch` lowers to an `ifte` dispatch chain wrapped in this, so `break` ends only the switch while `continue` keeps propagating to the enclosing loop. |
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
inductive Dialect | python | cLike | javascript | java | go
```

Every program carries the dialect the transpiler inferred (`render_lean.py` infers it from
the file extension: `.py` → `.python`; `.c`/`.h`/`.cpp`/`.cc`/`.cxx`/`.hh`/`.hpp` →
`.cLike`; `.java` and `.kt` → `.java`, Kotlin sharing Java's integer model; `.go` → `.go`;
`.js`/`.ts`/`.tsx`/`.jsx`/`.mjs`/`.cjs` → `.javascript`). An unrecognized extension, or a
mix of dialects in one program, is a refusal rather than a default — `DIALECT` and
`infer_dialect` in `cartographer/render_lean.py`. Arithmetic and string semantics are
parameterized by it.

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
  `ast-<Module>.json` and are what the ledger's holes-by-cause table counts. The
  `generator:*` and `genexpr:*` labels differ in origin only: `cartographer/generator_lowering.py`,
  the lowering pass that compiles `yield` to suspended frames, places them, and they are
  counted like every other static hole.
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
| `op:addressOf:<shape>:<kind>` | C `&x` that the `<operator>.addressOf` case of `cartographer/compiler/SourceCompiler.scala` could lower neither to an identity (`&aggregate`, `&function`, a boxed local) nor to `Expr.irefIndex`/`irefField` (`&a[i]`, `&s.f`, `&p->f` and their chained forms) nor to `Expr.strFrom` (`&z[i]` on a tracked byte cursor). `<shape>` is the operand (`addrShape`): `local`, `field`, `element`, `call`, else the CPG node label. `<kind>` classifies its static type (`addrKind`): `pointer`, `object`, `scalar`, `opaque-type` (a type name with no evidence behind it) or `unknown-type` (Joern recovered no type at all). One refinement replaces `unknown-type` when it applies: `pointer`, when the same name is read through `->` elsewhere in the method. An `&x` that is the direct argument of a call to a function outside the program (`scanf("%d", &n)`) still reads `unknown-type` although `STRATEGY.md` §41 shows it is a corpus-boundary gap, not a type-inference one; the exporter has the predicate (`addressOfFeedsExternalCall`) but does not yet use it, because any change to the exporter's source invalidates the provenance of every tracked AST until each is re-exported (`scripts/check_provenance.py`), so the relabelling waits for the next full re-export (see "Open items" in `STRATEGY.md`). Older ASTs carry the historical bare `op:addressOf` at the same sites. | Mixed: `scalar`/`opaque-type`/`unknown-type` are type-recovery or location-model work (`docs/languages.md`); the external-call case is the effect boundary the assurance case declares. |
| `op:delete-index`, `op:delete-slice`, `op:delete-field`, `op:delete-slice-shape`, `op:delete-shape` | `del d[k]`, slice deletion, attribute deletion. | Under Python, `del xs[i]` / `del d[k]` is `Stmt.delIndex` and `del xs[lo:hi:st]` is `Stmt.delSlice` (the `<operator>.delete` case of `cartographer/compiler/SourceCompiler.scala`, Python only because only Python boxes). What still holes: `op:delete-index` and `op:delete-slice` under every other dialect, where a container is a value with no identity to delete from; `op:delete-slice-shape` for a slice with other than three bounds; `op:delete-field` (`del o.f`, which Core's `del` cannot express) and `op:delete-shape` under all dialects. |
| `op:dictLiteral-nonempty`, `op:stringExpressionList`, `op:fieldAccess-shape` | CPG node shapes the exporter does not recognise. | Not yet implemented. |
| `op:raise-bare` | A bare `raise` **outside** an `except` handler; Core has no ambient current-exception. | Inside a handler a bare `raise` is translated: `pythonRaise` in `cartographer/compiler/SourceCompiler.scala` re-raises the handler's pending value (reference §7.8), so the label occurs only for a bare `raise` with no enclosing handler, under Python and under every other dialect. |
| `op:raise-cause` | An explicit Python exception cause. | Cause evaluation and exception chaining remain unsupported. |
| `op:raise-source-metadata`, `op:raise-shape`, `op:raise-constructor-shape` | Python raise metadata or operand shape cannot be recovered faithfully. | Refuses to treat an arbitrary value as a valid exception. |
| `raise:ambiguous-exception-value` | A dynamically raised value is a string naming a represented exception class. | Core cannot distinguish that string from an exception instance. |
| `raise:unmodelled-object`, `raise:unmodelled-callable` | A dynamically raised object or callable cannot be classified. | Requires exception-instance or class semantics. |
| `exception:<class>:details-iterator`, `exception:<class>:unmodelled-class` | An exception constructor needs unsupported iteration or class semantics. | Refuses to guess the constructor outcome. |
| `exception:<class>:details-version-dependent` | `SyntaxError`/`IndentationError` with a 7-field details iterable: `TypeError` on CPython 3.10-3.13, accepted on 3.14. | Core has no Python-version parameter; refuses to pick one interpreter's answer. |
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
| ~~`scope:class-closure`~~ | A class defined inside a function whose methods read the enclosing scope. **Closed**: `Expr.classClosure` / `Val.clsClos` express it (STRATEGY.md records the count going 18 → 0). The label is emitted nowhere in `cartographer/`, `scripts/` or `Autoform/`. | Implemented. |
| `assign:arity`, `assign:lhs:<shape>`, `assign:aug-impure-target`, `assign:aug-impure-receiver` | Multiple assignment targets, assignment to a shape Core has no statement for, and augmented assignment whose target or receiver would have to be evaluated twice. | Mostly not yet implemented; the "impure" ones are a correctness refusal, not a gap. |
| `call:no-callee-name` | A call whose callee the CPG left unnamed and that is not itself a call. | `call:computed-callee` is retired: a callee that is itself a call (`f(x)(y)`, `d["k"](3)`) is `Expr.callValue`, which applies what the callee evaluates to (a function, closure or boxed function object; a class value constructs an instance through the `alloc` rule) and holes `call:value:not-callable` at run time on anything else. |
| `call:effect-after-starred` | A starred argument followed by an argument with lifted assignments or increments. Saving the iterable would not preserve the timing of its expansion. | Explicit unsupported evaluation order. |
| `import:module-value`, `import:unresolved`, `import:absent:external`, `import:absent:prefix-in-cpg`, `import:absent:relative` | A module used as a value, or an import the CPG could not resolve. The `absent:` labels split the second case by *why*: the module is external to the CPG, a proper prefix of its path is in the CPG (so more resolver work could reach it), or it is a relative import whose target is missing. | Permanent for genuinely external modules; that is the boundary the assurance case declares. `absent:prefix-in-cpg` is the part that is not permanent. |
| `lit:float`, `lit:unquoted` | A float literal unsupported by the source exporter and a literal it could not decode. | Core has float values; source-literal translation still needs coverage. |
| `expr:BLOCK`, `expr:BLOCK-impure`, `expr:BLOCK-prelude`, `expr:empty-block`, `expr:genExp`, `expr:setComp`, `expr:comprehension-position`, `expr:<label>` | Statement-expressions. List/dict comprehensions lower (languages §10.6); `expr:genExp` remains a legacy refusal in positions that cannot carry a prelude. Recognized generator expressions compile to suspended frames; `setComp` has no Core set value; `comprehension-position` has no prelude slot. | Mixed. |
| `genexpr:source-metadata`, `genexpr:outer-loop-shape`, `genexpr:yield-shape`, `genexpr:free-variable-cells`, `genexpr:async` | Missing or ambiguous source scope, an unrecognized frontend lowering, captured shared cells or asynchronous iteration. A recognised generator expression whose factory the frame compiler then refuses carries that `generator:*` label (below) as an `Expr.hole` at the expression site instead. | Explicit generator-expression gaps. |
| `generator:closure-frame`, `generator:free-variable-cells`, `generator:async`, `generator:missing-metadata` | `cartographer/generator_lowering.py` refuses the whole generator function, whose body becomes one `Stmt.hole`: it defines a nested function or class (a closure would snapshot the frame's locals), it reads a free variable (a suspended free variable must keep the enclosing cell, not a copy), it is `async`, or the exporter saw `yield` without recording the lexical generator metadata. | Explicit generator gaps; free variables need shared cells. |
| `generator:yield-expression-shape`, `generator:breakBlock`, `generator:control-graph-size`, `generator:control-graph-depth` | A `yield` nested inside another expression, a `breakBlock` inside a generator body, or a control graph past the lowering's limits (4,096 resume points, 128 nesting levels). Whole-function refusals, like the row above. | Resource limits and unsupported shapes, named rather than approximated. |
| `generator:yieldFromS` | A `yield from it` anywhere in a generator body refuses the whole frame (`cartographer/generator_lowering.py`, the same arm as `breakBlock`). The statement-position case has a faithful lowering on paper -- `iter()` once, each item re-yielded through a `forIn`, `StopIteration` ending the delegation, with only the forwarding of a non-`None` `send()` value left as a hole -- but it was not landed on 2026-11-13: `generator_lowering.py` runs inside `render_lean.py`, so the change re-renders every corpus with a `yield from` (requests, click, jinja2), and `scripts/check_render.py` requires those renders, their ledgers, the pinned Lean ledger fixtures and their spec modules to be regenerated in the same commit (`CONTRIBUTING.md`). It waits for a dedicated re-land; see "Open items" in `STRATEGY.md`. | Open: the re-land above; the value-used case (`x = yield from it`) additionally needs exception payloads (`StopIteration.value`). |
| `generator:close`, `generator:throw`, `generator:return-value`, `generator:invalid-continuation` | Holes inside an otherwise lowered frame: `close()` and `throw()` on a suspended frame, a `return <value>` reaching the terminal (the value would have to travel in `StopIteration`; also mirrored into `analysisBody`), and a resume at an instruction position the dispatch does not know (a lowering bug if it ever appears). | Return values need exception payloads; `close`/`throw` need exception injection at the suspension point. |
| `cstr:pointer-arith`, `cstr:address-compare`, `cstr:address-equality` | C string operations that are pointer operations, refused rather than given the Python answer. | **Permanent by design** until Core models addresses. |
| `op:is-type-test`, `op:is:unknown-type`, `op:is:value-position`, `op:when:is-type-test`, `op:when:is:unknown-type`, `op:when:enum-entry`, `op:safe-call:receiver-unread`, `op:safe-call:value-position`, `op:elvis:*`, `op:when:*` | Kotlin: a type Core has no test op for (`Int`/`Long` share `.int`, an analysed class needs the hierarchy), one with no declaration here to read (a platform or erased type), an enum-entry disjunction whose subject is not pure, an entry of an enum the analysed code does not declare, a `?.` whose receiver the lowering did not read through its temporary or that sits where there is no prelude for one, and the `when`/`?:` shapes listed in `docs/languages.md` ("Kotlin `when` and `?:`", "Kotlin `is`"). | Mixed: the type tests Core can decide are lowered; the rest need a value-tag/class test op or the class hierarchy. |
| `stmt:<label>`, `stmt:UNKNOWN:<...>` | A CPG statement node with no mapping. The `UNKNOWN` bucket is where new front-end shapes appear. | Not yet implemented. |

### Runtime labels (interpreter)

| Label | Raised when |
|---|---|
| `call:<name>` | The callee resolves neither in the program, nor as a value in scope, nor in the modelled stdlib. In the AST a call to an untranslated function is indistinguishable from a call to a translated one, which is why the ledger reports call-closure separately from hole-freedom. |
| `call:python-defaults` | Default storage and definition-time evaluation remain unsupported. The exporter inserts a hole before the body, including calls which supply every argument. Recovered signatures without defaults support required, positional-only and keyword-only binding. Historical ASTs can still contain `call:python-positional-only` and `call:python-keyword-only` holes; re-export to recover their signatures. |
| `call:python-signature-shape` | Source parameter names disagree with the exported CPG parameter shape. The exporter refuses to guess a signature. Legacy models without `pythonSignature` retain historical binding behavior and need re-export before claiming source call fidelity. |
| `call:python-receiver-signature` | A method lacks an ordinary first positional `self` (`def f()`, `def f(*, self)`, `def f(*self)`, `def f(receiver, a)`) or has decorators whose descriptor binding is not modeled. A receiver followed by collectors (`def f(self, *args, **kwargs)`) is NOT a gap any more: the stripped receiver's name travels as `pythonSignature.receiverName` and `kwargsRejected` refuses a `self=` keyword that would otherwise vanish into `**kwargs`. Placeholder argument collectors ensure the explicit gap is reached instead of producing an incorrect arity exception. They do not claim that the source method accepts arbitrary arguments. A positional-only `self` can still be modeled with `**kwargs`. |
| `call:python-decorator-binding` | Retained as the exporter's fallback for a decorated definition that is neither applied nor refused under a more specific name; no current source shape reaches it. A decorator the program defines is applied at definition time (Language Reference §8.7): the raw body is exported as `<name><undecorated>` (`undecoratedOf` names the source spelling), the defining scope binds `name = d1(d2(<raw>))` with every decorator read as a value, and a module-level function or a method of a module-level class gets an auxiliary source entry (`decoratedEntries`) that forwards `(*args, **kwargs)` to the rebound binding. `tests/test_python_decorators.py`. |
| `decorator:external:<name>` | A decorator from outside the program (`functools.wraps(f)`, `contextlib.contextmanager`). Its meaning is not guessed; the definition keeps this gap until a contract models it (Milestone 3). |
| `decorator:class-body:nested-class`, `decorator:class-body:class-local-name`, `decorator:class-body:expression-shape`, `decorator:class-body:redefined-member` | A class-body decorator the exporter cannot apply faithfully in the module scope: the class is not at module level, a decorator expression reads a name the class body binds (or the class's own name), contains a scoped or suspending expression, or the member is bound twice. The class attribute stays opaque (`class-attribute:decorator`). |
| `class-attribute:<attr>:descriptor-object` | A stored class attribute (a decorated method's value) that may implement the descriptor protocol: an instance of a recovered class whose namespace does not prove `__get__`/`__set__`/`__delete__` absent, or an external value. Reads and writes through an instance are gaps. A stored FUNCTION binds as a method (`Ctx.storedAttributeValue`, reserved closure `<bound-method>.<function>`). |
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
| `in:javascript-property`, `in:javascript-object-property` | JavaScript `in` (property presence) on an array with a non-integer key, or on an object/`Map`, whose prototype the model does not carry. |
| `forIn:non-iterable` | Iterating a non-iterable. |
| `iterator:dict-keys-changed` | A dictionary's key layout changed without changing its size; CPython slot traversal is not represented. Value replacement is supported. |
| `iterator:sentinel-identity` | Callable/sentinel iteration needs identity that Core cannot decide and that can affect equality, such as two unboxed NaNs. |
| `iterator:exception-hierarchy` | A sequence or callable iterator caught a user exception whose ancestry its synthetic handler cannot determine. |
| `iterator:result-protocol` | An `__iter__` result has no translated `__next__`, but inherited or metaclass behavior is not represented well enough to prove it absent. Known non-iterator builtin results raise `TypeError`. |
| `iterator:length-hint`, `iterator:sum-type` | A consumer needs an observable custom length hint or accumulation outside the exact integer model. |
| `iterator:invalid-index`, `iterator:source-kind-changed`, `iterator:dangling-reference` | A malformed internal iterator state. Source-created iterators keep these fields private. |
| `setIndex:immutable-containers` | `e[i] = v` on a container *value* — a literal under a dialect that does not box (a C aggregate initializer has no identity to share) — or on an instance whose class defines no `__setitem__`. Under `.python` and `.javascript` list and dict literals allocate, so the write goes through the payload and this label is not reached (`docs/boxed-containers.md`). |
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
  all one feature, boxed mutable containers, **landed for Python and JavaScript**
  (`docs/boxed-containers.md`). What is left of them is the non-boxing dialects, where a
  container literal is a value on purpose, plus `op:delete-field` / `op:delete-shape`,
  which no dialect translates.
* `lit:float` and remaining float skips in the differential oracle — source-literal
  translation and runtime value encoding beyond the supported cases.
* `control:TRY-*` beyond the translated shapes — a richer control-flow encoding.
* `call:<name>` for stdlib callees — more of `Stdlib.lean`. This is the largest single
  lever on the verifiable core, because a function is only as analysable as its callees.
* The `expr:`, `stmt:`, `op:` generic buckets — ordinary exporter work.

The governing rule: **an honest hole with a precise label beats a wrong translation.** A
hole is counted, declared, and blocks proof at exactly the right point. A wrong
translation is invisible until an oracle happens to look.
