import Lean
import Autoform.Lang.Core.Semantics

/-!
# Trust ledger

The deliverable is never "your codebase is verified". It is a precise statement of what
was translated, what was assumed, and what remains — so a reader can locate the trust
boundary in seconds.

Evidence types here are the domain-specific part (§10 of `STRATEGY.md`); the argument
structure they feed is SACM's, not ours.
-/

namespace Autoform.Core

open Std

/-!
## Static hole-freedom is an upper bound, not a guarantee

`Func.total` (no `Expr.hole`/`Stmt.hole` in the AST) was being reported as "the verifiable
core". Testing showed that claim is too strong: the *interpreter* can introduce holes at
runtime that static counting cannot see.

    def sneaky  := .ret (.field (.name "x") "attr")   -- Func.total = true
    run sneaky 3  ==>  hole "field:attr:non-object"
    run sneaky2 3 ==>  hole "call:not_translated"     -- unresolved call, statically invisible
    run sneaky3 3 ==>  hole "index:unsupported"

The worst of the three is `call:` — a call to a function that was never translated looks
identical, in the AST, to a call to one that was. So the headline coverage number
overstated the verifiable core, and this refines it.

Three tiers are now reported, weakest claim first:

* **hole-free** — no static holes. An upper bound on what could be verified.
* **call-closed** — hole-free *and* every call/method target resolves inside the program.
  Removes the invisible-`call:` failure mode.
* **dynamic-hole risk** — constructs (`field`, `index`, `mcall`, arithmetic that can hit
  `ub`) that can still produce a hole on some input. Reported as a count, not subtracted,
  because whether they *do* is input-dependent and belongs to the conformance oracle.
-/

namespace Analysis

mutual
/-- Names called by an expression, via `call` or `mcall`. -/
def eCalls : Expr → List (Bool × String)
  | .call f as    => (false, f) :: eCallsL as
  | .mcall r m as => (true, m) :: eCalls r ++ eCallsL as
  | .binop _ a b  => eCalls a ++ eCalls b
  | .unop _ a     => eCalls a
  | .index a b    => eCalls a ++ eCalls b
  | .field a _    => eCalls a
  | .alloc _ as   => eCallsL as
  | .listE as     => eCallsL as
  | .tupleE as    => eCallsL as
  | .dictE kvs    => eCallsP kvs
  | .cond c a b   => eCalls c ++ eCalls a ++ eCalls b
  | .isOp _ a b   => eCalls a ++ eCalls b
  | .inOp _ a b   => eCalls a ++ eCalls b
  -- A Python list/dict display: calls inside it are calls of the function.
  | .boxContainer a => eCalls a
  | _             => []
/-- Names called across a list of expressions. -/
def eCallsL : List Expr → List (Bool × String)
  | []      => []
  | e :: es => eCalls e ++ eCallsL es
/-- Names called across key/value pairs. -/
def eCallsP : List (Expr × Expr) → List (Bool × String)
  | []           => []
  | (k, v) :: ps => eCalls k ++ eCalls v ++ eCallsP ps
end

mutual
/-- Constructs that can produce a hole at runtime even when the AST has none. -/
def eRisk : Expr → Nat
  | .field a _    => 1 + eRisk a
  | .index a b    => 1 + eRisk a + eRisk b
  | .mcall r _ as => 1 + eRisk r + eRiskL as
  | .binop _ a b  => 1 + eRisk a + eRisk b   -- may hit `ub:` under a fixed-width dialect
  | .call _ as    => 1 + eRiskL as           -- may fail to resolve
  | .unop _ a     => eRisk a
  | .alloc _ as   => 1 + eRiskL as
  | .listE as     => eRiskL as
  | .tupleE as    => eRiskL as
  | .dictE kvs    => eRiskP kvs
  | .cond c a b   => eRisk c + eRisk a + eRisk b
  | .isOp _ a b   => eRisk a + eRisk b
  | .inOp _ a b   => 1 + eRisk a + eRisk b
  | .boxContainer a => eRisk a
  | _             => 0
/-- Risk across a list of expressions. -/
def eRiskL : List Expr → Nat
  | []      => 0
  | e :: es => eRisk e + eRiskL es
/-- Risk across key/value pairs. -/
def eRiskP : List (Expr × Expr) → Nat
  | []           => 0
  | (k, v) :: ps => eRisk k + eRisk v + eRiskP ps
end

/-- Names called by a statement. -/
def sCalls : Stmt → List (Bool × String)
  | .expr e         => eCalls e
  | .assign _ e     => eCalls e
  | .setField r _ v => eCalls r ++ eCalls v
  | .setIndex r i v => eCalls r ++ eCalls i ++ eCalls v
  | .delIndex r i   => eCalls r ++ eCalls i
  | .seq a b        => sCalls a ++ sCalls b
  | .ifte c a b     => eCalls c ++ sCalls a ++ sCalls b
  | .loop c a       => eCalls c ++ sCalls a
  | .forIn _ e b    => eCalls e ++ sCalls b
  | .ret e          => eCalls e
  | .tryCatch b _ h => sCalls b ++ sCalls h
  | .raise e        => eCalls e
  | _               => []

/-- Names a statement binds in the function's own scope: assignment targets, loop
variables, exception names. Used only under Python's scoping rules (STRATEGY.md §62),
where a bare call name is a variable rather than a function-table key. -/
def sBinds : Stmt → List String
  | .assign x _     => [x]
  | .forIn x _ b    => x :: sBinds b
  | .tryCatch b x h => x :: sBinds b ++ sBinds h
  | .tryFinally b f => sBinds b ++ sBinds f
  | .seq a b        => sBinds a ++ sBinds b
  | .ifte _ a b     => sBinds a ++ sBinds b
  | .loop _ a       => sBinds a
  | .breakBlock a   => sBinds a
  | _               => []

/-- Runtime-hole risk of a statement. -/
def sRisk : Stmt → Nat
  | .expr e         => eRisk e
  | .assign _ e     => eRisk e
  | .setField r _ v => 1 + eRisk r + eRisk v
  | .setIndex _ _ _ => 1
  | .delIndex _ _   => 1
  | .seq a b        => sRisk a + sRisk b
  | .ifte c a b     => eRisk c + sRisk a + sRisk b
  | .loop c a       => eRisk c + sRisk a
  | .forIn _ e b    => 1 + eRisk e + sRisk b
  | .ret e          => eRisk e
  | .tryCatch b _ h => sRisk b + sRisk h
  | .raise e        => eRisk e
  | _               => 0

end Analysis

/-- Calls in this function, each tagged with the dispatch path the interpreter will
take: `true` for a method call (`mcall`, resolved by `Ctx.resolveMethod`), `false` for a
free call (`call`, resolved by `Ctx.resolve`). The tag is the whole point — the two paths
have *different* resolution rules, and a flat `List String` cannot say which applies. -/
def Func.calls (f : Func) : List (Bool × String) := Analysis.sCalls f.body

/-- The function's own local names: parameters and what its body binds. -/
def Func.localNames (f : Func) : List String := f.params ++ Analysis.sBinds f.body

/-- How many constructs in this function could hole at runtime. -/
def Func.risk (f : Func) : Nat := Analysis.sRisk f.body

/-- Can the interpreter resolve this callee, on the path it will actually take?

Must mirror what `evalExpr` actually does — neither stricter nor looser. The two call
paths do not agree, and collapsing them is how this went wrong twice in opposite
directions:

* **Too strict.** `Ctx.resolve` requires a *unique* suffix match, and applying that rule
  to method calls reported `clear` (9 candidate methods), `__init__` (22) and `pop` (3)
  as unresolvable while the interpreter dispatches them fine — understating the core by
  14 functions. A ledger stricter than the artifact it describes is wrong in the *safe*
  direction, which makes it easy to leave unnoticed, but it still hides the real gap.

* **Too loose.** The fix for that applied `resolveMethod`'s first-match rule to *free*
  calls as well, and `scripts/core_oracle.py` refuted it by execution: `_wrapper` and
  `cache_clear` have several definitions, so the ledger called them resolvable while
  `Ctx.resolve` — which the `call` path really uses — returns `none` on the ambiguity and
  the interpreter holes. That loosening is most of why the claimed core jumped 45 → 74.

So the predicate now takes the dispatch tag from `Func.calls` and answers per path. -/
def Ctx.resolvable (isMethod : Bool) (ctx : Ctx) (n : String) : Bool :=
  if isMethod then
    -- Mirrors `Ctx.resolveMethod`, which takes the *first* match. Still an upper bound:
    -- it asks only whether some class defines the name, not whether *this* receiver's
    -- class does — a static ledger has no receiver.
    ctx.table.any (fun q => q.1.endsWith ("." ++ n))
  else
    -- Mirrors `Ctx.resolve` exactly, ambiguity and all: two suffix matches resolve to
    -- nothing, so two matches must not count as resolvable.
    (ctx.resolve n).isSome
    -- Modelled builtins are resolvable too. `knowsFree` is exact at the name level and is
    -- the *guard* in front of `builtin`, so an unlisted case is dead code rather than a
    -- ledger overstatement — the drift direction that matters cannot rot.
    --
    -- `knowsMethod` is deliberately NOT consulted. It is only an upper bound: methods are
    -- modelled per receiver shape (`pop` is answered on a dict, refused on a str), and a
    -- static ledger has no receiver. Its author measured the pure methods as worth +1
    -- function, so excluding them costs almost nothing and buys an honest number.
    || Stdlib.knowsFree ctx.dialect n

/-- `Ctx.resolvable` for a call made from a function whose local names are `locals`.

Under Python's scoping rules (`Ctx.scopedName`: a Python program with a class table, and
an unqualified name) the interpreter never consults the function table for a free call:
the callee is the local of that name, else a module global, else a builtin
(`Ctx.calleeVal`). The ledger has no globals frame and no captured environment, so it
counts such a call as resolvable only when the name is one of the caller's own locals or a
modelled builtin. That is *stricter* than the interpreter (a captured or global binding
also works there), which is the safe direction for a claimed core; the legacy suffix rule
would be looser than it (a unique `….n` in the table is exactly what Python scoping
ignores). Every other call keeps `Ctx.resolvable`. -/
def Ctx.resolvableIn (ctx : Ctx) (locals : List String) (isMethod : Bool) (n : String) :
    Bool :=
  if !isMethod && ctx.scopedName n then locals.contains n || Stdlib.knowsFree ctx.dialect n
  else ctx.resolvable isMethod n

/-! ## Making call closure linear instead of quadratic

`Ctx.resolvable` calls `Ctx.resolve`, which scans the whole function table on every miss.
The ledger asks it once per call site, so computing call closure is O(callsites × table)
— 363 s on a 10k-function corpus.

The obvious fix, a `HashMap` field on `Ctx`, is **not available**: the proofs in
`Autoform/Contracts.lean`, `Autoform/Refine.lean` and `Autoform/CallingConvention.lean`
`simp` through `Ctx.resolve.go` on the association list, so the list shape is load-bearing
for the kernel. So the index lives *here*, is built once per program, and `Ctx.resolve`
itself is untouched — a `git diff` of `Semantics.lean` shows no change to it.

An index is only a speedup if it computes the same answer. It would be very easy for this
one to quietly disagree with `Ctx.resolvable` and inflate the verifiable core, which is
the exact §17/§30 failure this project keeps catching, so:

* the equivalence argument is written out below, in terms of `String.endsWith`;
* `Program.callClosureAgrees` re-derives the answer *both* ways and compares, and
  `#guard`s at the bottom of this file run it on real corpora at elaboration time. A
  disagreement is a build failure, not a silent number.

**The equivalence.** `Ctx.resolve n` looks for an exact key, then for a *unique* key with
`k.endsWith ("." ++ n)`. For a key `k` split on `"."` into `p₀ … pₘ`, the strings `k` ends
with after a dot are exactly the rejoined tails `p₁…pₘ`, `p₂…pₘ`, …, `pₘ` — one per dot,
all of different lengths, so a single key contributes each candidate `n` at most once.
Therefore `suffixCount[n]` counts *keys*, and:

* `(ctx.resolve n).isSome  ↔  exact.contains n ∨ suffixCount[n] = 1`
* `ctx.table.any (·.1.endsWith ("." ++ n))  ↔  suffixCount[n] ≥ 1`

which is what `ResolveIndex.resolvable` evaluates. -/
structure ResolveIndex where
  /-- Keys present verbatim in the table — the exact-match arm of `Ctx.resolve`. -/
  exact : Std.HashSet String
  /-- For each name that some key ends with after a dot, how many keys do. `1` means
  `Ctx.resolve`'s uniqueness condition holds; `≥ 2` means it resolves to `none`. -/
  suffixCount : Std.HashMap String Nat
  deriving Inhabited

/-- Every string `k` ends with immediately after a `'.'`, longest first. `"a.b.c"` gives
`["b.c", "c"]` — and notably *not* `"a.b.c"` itself, matching `endsWith ("." ++ n)`, which
requires a dot to be present. -/
private def nonEmptySuffixes : List String → List (List String)
  | []      => []
  | p :: ps => (p :: ps) :: nonEmptySuffixes ps

def dottedTails (k : String) : List String :=
  match k.splitOn "." with
  | []      => []
  | _ :: ps => (nonEmptySuffixes ps).map (fun t => ".".intercalate t)

def ResolveIndex.build (t : FuncTable) : ResolveIndex :=
  t.foldl (fun idx (k, _) =>
    { exact := idx.exact.insert k
    , suffixCount := (dottedTails k).foldl
        (fun m n => m.insert n ((m.getD n 0) + 1)) idx.suffixCount })
    { exact := ∅, suffixCount := ∅ }

/-- The index's answer to `Ctx.resolvable`. Mirrors it arm for arm, including the
`Stdlib.knowsFree` fallback and the deliberate omission of `knowsMethod`. -/
def ResolveIndex.resolvable (idx : ResolveIndex) (dialect : Dialect)
    (isMethod : Bool) (n : String) : Bool :=
  if isMethod then idx.suffixCount.getD n 0 ≥ 1
  else idx.exact.contains n || idx.suffixCount.getD n 0 == 1
       || Stdlib.knowsFree dialect n

/-- The index's answer to `Ctx.resolvableIn`; `strict` is `Ctx.pyStrict` of the program. -/
def ResolveIndex.resolvableIn (idx : ResolveIndex) (dialect : Dialect) (strict : Bool)
    (locals : List String) (isMethod : Bool) (n : String) : Bool :=
  if !isMethod && (strict && isPyIdent n) then locals.contains n || Stdlib.knowsFree dialect n
  else idx.resolvable dialect isMethod n

/-- Whether a program runs under Python's scoping rules (`Ctx.pyStrict` of its context). -/
def Program.pyStrict (p : Program) : Bool := p.pyClasses.isSome && p.dialect == .python

/-- Hole-free **and** every call target resolves inside the program.

The reference definition: `Ctx.resolvable` per call site, quadratic. Kept because it is
the one that obviously mirrors the interpreter, and because it is the thing
`Program.callClosureAgrees` checks the index against. -/
def Program.callClosedRef (p : Program) : List Func :=
  let ctx : Ctx := { dialect := p.dialect, table := p.table, pyClasses := p.pyClasses }
  p.verifiableCore.filter (fun f =>
    f.calls.all (fun c => ctx.resolvableIn f.localNames c.1 c.2))

/-- Hole-free **and** every call target resolves inside the program, via the index. This
is what the ledger reports. -/
def Program.callClosed (p : Program) : List Func :=
  let idx := ResolveIndex.build p.table
  p.verifiableCore.filter (fun f =>
    f.calls.all (fun c => idx.resolvableIn p.dialect p.pyStrict f.localNames c.1 c.2))

/-- Do the two agree, function for function? Compares the *names*, not just the counts:
two lists of equal length can still be different lists, and it is the membership that the
ledger's claim rests on. -/
def Program.callClosureAgrees (p : Program) : Bool :=
  p.callClosed.map (·.name) == p.callClosedRef.map (·.name)

/-! ## Conditionally verifiable functions, and one named assumption per hole

`docs/contracts.md`. A function with holes is not verifiable *unconditionally*, but it can
be reasoned about **relative to contracts on its holes** (`Autoform/Contracts.lean` for
expression holes, `Autoform/HoleContracts.lean` for statement holes). The ledger reports
such functions as a **separate** number, never folded into the verifiable core:

* **conditionally verifiable** — at least one hole, and every call target resolves (the
  same per-path resolution test as `callClosed`). An *upper bound*, exactly as hole-free
  is for the core: it says a contract-relative statement is expressible, not that one has
  been proved. Proved ones are counted separately, from `contracts-<Module>.json`.
* **named hole assumptions** — every hole occurrence in the program gets an identifier
  `H:<function>#<i>:<label>` and a kind (`stmt`/`expr`). Nothing is silently trusted: a
  contract-relative result must name which of these it assumes, and `holeSites_labels`
  proves the inventory is exactly `Stmt.holes` — no occurrence can be missing from it. -/

namespace Analysis

mutual

/-- Every hole in a statement with its position: `true` for a `Stmt.hole`, `false` for an
`Expr.hole`. Mirrors `Stmt.holes` arm for arm (`holeSites_labels`). -/
def sHoleSites : Stmt → List (Bool × String)
  | .hole l          => [(true, l)]
  | .expr e          => e.holes.map (false, ·)
  | .assign _ e      => e.holes.map (false, ·)
  | .setField r _ v  => (r.holes ++ v.holes).map (false, ·)
  | .setIndex r i v  => (r.holes ++ i.holes ++ v.holes).map (false, ·)
  | .delIndex r i    => (r.holes ++ i.holes).map (false, ·)
  | .delSlice r s e st => (r.holes ++ s.holes ++ e.holes ++ st.holes).map (false, ·)
  | .setDerefIref p v => (p.holes ++ v.holes).map (false, ·)
  | .seq a b         => sHoleSites a ++ sHoleSites b
  | .ifte c a b      => c.holes.map (false, ·) ++ sHoleSites a ++ sHoleSites b
  | .loop c a        => c.holes.map (false, ·) ++ sHoleSites a
  | .breakBlock a    => sHoleSites a
  | .forIn _ e b     => e.holes.map (false, ·) ++ sHoleSites b
  | .ret e           => e.holes.map (false, ·)
  | .tryCatch b _ h  => sHoleSites b ++ sHoleSites h
  | .tryFinally b f  => sHoleSites b ++ sHoleSites f
  | .multiCatch b hs => sHoleSites b ++ sHoleSitesHandlers hs
  | .raise e         => e.holes.map (false, ·)
  | .setGlobal _ e   => e.holes.map (false, ·)
  | _                => []

/-- Hole sites across `multiCatch` handlers. Kept explicit so Lean sees structural recursion. -/
def sHoleSitesHandlers : List (String × Stmt) → List (Bool × String)
  | [] => []
  | (_, h) :: hs => sHoleSites h ++ sHoleSitesHandlers hs

end

mutual

/-- The site inventory is complete and exact: its labels are `Stmt.holes`, in order. -/
theorem holeSites_labels : (s : Stmt) → (sHoleSites s).map (·.2) = s.holes
  | .hole l => by simp [sHoleSites, Stmt.holes]
  | .expr e => by simp [sHoleSites, Stmt.holes, List.map_map, Function.comp_def]
  | .assign x e => by simp [sHoleSites, Stmt.holes, List.map_map, Function.comp_def]
  | .setField r f v => by simp [sHoleSites, Stmt.holes, List.map_map, Function.comp_def]
  | .setIndex r i v => by simp [sHoleSites, Stmt.holes, List.map_map, Function.comp_def]
  | .delIndex r i => by simp [sHoleSites, Stmt.holes, List.map_map, Function.comp_def]
  | .delSlice r s e st => by simp [sHoleSites, Stmt.holes, List.map_map, Function.comp_def]
  | .setDerefIref p v => by simp [sHoleSites, Stmt.holes, List.map_map, Function.comp_def]
  | .seq a b => by simp [sHoleSites, Stmt.holes, holeSites_labels a, holeSites_labels b]
  | .ifte c a b => by simp [sHoleSites, Stmt.holes, holeSites_labels a, holeSites_labels b, List.map_map, Function.comp_def]
  | .loop c a => by simp [sHoleSites, Stmt.holes, holeSites_labels a, List.map_map, Function.comp_def]
  | .breakBlock a => by simp [sHoleSites, Stmt.holes, holeSites_labels a]
  | .forIn x e b => by simp [sHoleSites, Stmt.holes, holeSites_labels b, List.map_map, Function.comp_def]
  | .ret e => by simp [sHoleSites, Stmt.holes, List.map_map, Function.comp_def]
  | .brk => by simp [sHoleSites, Stmt.holes]
  | .cont => by simp [sHoleSites, Stmt.holes]
  | .tryCatch b x h => by simp [sHoleSites, Stmt.holes, holeSites_labels b, holeSites_labels h]
  | .tryFinally b f => by simp [sHoleSites, Stmt.holes, holeSites_labels b, holeSites_labels f]
  | .multiCatch b hs => by simp [sHoleSites, Stmt.holes, holeSites_labels b, holeSitesHandlers_labels hs]
  | .raise e => by simp [sHoleSites, Stmt.holes, List.map_map, Function.comp_def]
  | .del x => by simp [sHoleSites, Stmt.holes]
  | .setGlobal x e => by simp [sHoleSites, Stmt.holes, List.map_map, Function.comp_def]
  | .declGlobal x => by simp [sHoleSites, Stmt.holes]
  | .skip => by simp [sHoleSites, Stmt.holes]

/-- The handler-site inventory is complete and exact. -/
theorem holeSitesHandlers_labels : (hs : List (String × Stmt)) →
    (sHoleSitesHandlers hs).map (·.2) = Stmt.holesHandlers hs
  | [] => by simp [sHoleSitesHandlers, Stmt.holesHandlers]
  | (_, h) :: hs => by
      simp [sHoleSitesHandlers, Stmt.holesHandlers, holeSites_labels h, holeSitesHandlers_labels hs]

end

end Analysis

/-- Hole occurrences of a function, tagged `true` for statement position: the body's,
then those in non-constant parameter defaults (`Func.defaults`, expression position) —
the same order as `Func.holes`. -/
def Func.holeSites (f : Func) : List (Bool × String) :=
  Analysis.sHoleSites f.body ++ (f.defaults.flatMap (·.2.holes)).map (false, ·)

/-- The per-function inventory is exactly `Func.holes`: a hole in a parameter default is
named like any other, so no occurrence the ledger counts can be missing from it. -/
theorem Func.holeSites_labels (f : Func) : f.holeSites.map (·.2) = f.holes := by
  simp [Func.holeSites, Func.holes, Analysis.holeSites_labels, List.map_map,
    Function.comp_def]

/-- Has holes, and is otherwise call-closed: every hole is a place a named contract can be
assumed, and nothing else is missing. Disjoint from `callClosed` by construction. -/
def Program.conditionallyVerifiable (p : Program) : List Func :=
  let idx := ResolveIndex.build p.table
  p.funcs.filter (fun f =>
    !f.total && f.calls.all (fun c =>
      idx.resolvableIn p.dialect p.pyStrict f.localNames c.1 c.2))

/-- The name of the assumption for the `i`-th hole of `f`. -/
def holeAssumptionId (fn : String) (i : Nat) (label : String) : String :=
  s!"H:{fn}#{i}:{label}"

/-- One named assumption per hole occurrence, in program order. -/
def Program.holeAssumptionsJson (p : Program) : Lean.Json :=
  let cv := (p.conditionallyVerifiable.map (·.name))
  .arr <| (p.funcs.flatMap fun f =>
    (f.holeSites.zipIdx).map fun ((isStmt, l), i) =>
      Lean.Json.mkObj
        [ ("id",       .str (holeAssumptionId f.name i l))
        , ("function", .str f.name)
        , ("label",    .str l)
        , ("kind",     .str (if isStmt then "stmt" else "expr"))
        , ("conditionallyVerifiable", .bool (cv.contains f.name)) ]).toArray

/-- Per-program translation evidence. -/
structure Coverage where
  funcs      : Nat
  nodes      : Nat
  holes      : Nat
  totalFuncs : Nat
  /-- Hole-free *and* call-closed: the honest verifiable core. -/
  closedFuncs : Nat
  /-- Constructs that can still hole at runtime, across the whole program. -/
  riskNodes  : Nat
  byLabel    : List (String × Nat)
  deriving Repr

/-- Group hole labels by frequency, most common first. -/
def tally (ls : List String) : List (String × Nat) :=
  let m := ls.foldl (fun (m : Std.HashMap String Nat) l =>
    m.insert l ((m.getD l 0) + 1)) ∅
  (m.toList).mergeSort (fun a b => a.2 ≥ b.2)

/-- Compute coverage for a translated program. -/
def Program.coverage (p : Program) : Coverage :=
  let hs    := p.holes
  let nf    := p.funcs.length
  let nodes := p.size
  let core  := p.verifiableCore.length
  let closed := p.callClosed.length
  let risk   := (p.funcs.map Func.risk).sum
  { funcs      := nf
  , nodes      := nodes
  , holes      := hs.length
  , totalFuncs := core
  , closedFuncs := closed
  , riskNodes  := risk
  , byLabel    := tally hs }

/-- Render the ledger. Percentages are of AST nodes, and the verifiable core is the set
of functions with **no** holes — the only ones that can be verified unconditionally. -/
def Program.ledger (p : Program) (name : String) : String :=
  let c := p.coverage
  let cv := p.conditionallyVerifiable
  let cvHoles : Nat := (cv.map (·.holes.length)).sum
  let pct (a b : Nat) : String :=
    if b == 0 then "n/a" else s!"{(a * 100) / b}%"
  let hdr := s!"
╭─ autoform trust ledger ─ {name}
│ functions translated : {c.funcs}
│ AST nodes            : {c.nodes}
│ holes                : {c.holes}  ({pct c.holes c.nodes} of nodes)
│ hole-free (upper bd) : {c.totalFuncs} / {c.funcs} functions  ({pct c.totalFuncs c.funcs})
│ VERIFIABLE CORE      : {c.closedFuncs} / {c.funcs} functions  ({pct c.closedFuncs c.funcs}) — hole-free AND call-closed
│ CONDITIONALLY verif. : {cv.length} / {c.funcs} functions  ({pct cv.length c.funcs}) — call-closed but holed; results only RELATIVE TO {cvHoles} named hole assumptions, NOT in the core
│ dynamic-hole risk    : {c.riskNodes} constructs may hole at runtime (input-dependent)
│ semantics            : Autoform.Core (fuel-indexed, total, no sorry)
│ transpiler           : Joern CPG → Core, deterministic
│ NOT PROVED           : transpiler faithfulness — see conformance.json
├─ holes by cause ─────────────────────────────────────────────"
  let rows := c.byLabel.take 12 |>.map (fun (l, n) => s!"\n│ {n}  {l}")
  let more := if c.byLabel.length > 12 then s!"\n│         … {c.byLabel.length - 12} more labels" else ""
  hdr ++ String.join rows ++ more ++ "\n╰───────────────────────────────────────────────────────────────"

/-- Human-readable dialect name, for the ledger and for provenance in the assurance case. -/
def Dialect.name : Dialect -> String
  | .python     => "python"
  | .cLike      => "c-like"
  | .javascript => "javascript"

/-- Machine-readable ledger, for `scripts/sacm.py` to consume as evidence.

Built with `Lean.Json` rather than string concatenation, and tagged with the module and
dialect explicitly. The SACM pass caught exactly this class of defect in
`conformance.json`: evidence that cannot be attributed to a subject cannot support a
claim about that subject, and was correctly capped at WEAK. -/
def Program.ledgerJson (p : Program) (name : String) : Lean.Json :=
  let c := p.coverage
  let cv := p.conditionallyVerifiable
  let cvHoles : Nat := (cv.map (·.holes.length)).sum
  Lean.Json.mkObj
    [ ("module",         .str name)
    , ("dialect",        .str p.dialect.name)
    , ("functions",      .num c.funcs)
    , ("nodes",          .num c.nodes)
    , ("holes",          .num c.holes)
    , ("holeFree",       .num c.totalFuncs)
    , ("verifiableCore", .num c.closedFuncs)
    , ("dynamicHoleRisk", .num c.riskNodes)
    -- Reported apart from `verifiableCore`, never added to it: these functions are
    -- analysable only relative to named contracts on their holes (docs/contracts.md).
    , ("conditionallyVerifiable", .num cv.length)
    , ("conditionalAssumptions",  .num cvHoles)
    , ("holeAssumptions",         p.holeAssumptionsJson)
    , ("holesByLabel",   .arr (c.byLabel.map (fun (l, n) =>
        Lean.Json.mkObj [("label", .str l), ("count", .num n)])).toArray) ]

/-! ## The index, checked against the definition it replaces

A synthetic table covering every arm, including the two that a wrong index would get
wrong in the *flattering* direction: an ambiguous suffix must be unresolvable on the free
path, and a name that is only a *substring* of a key must not match at all. Real corpora
are checked too — `scripts/ledger.lean.tmpl` fails loudly if `callClosureAgrees` is false
for the module being reported. -/
section IndexCheck

private def tbl : FuncTable :=
  [ ("m.py:<module>.helper",      { name := "m.py:<module>.helper",   params := [], body := .skip })
  , ("m.py:<module>.A.clear",     { name := "m.py:<module>.A.clear",  params := [], body := .skip })
  , ("m.py:<module>.B.clear",     { name := "m.py:<module>.B.clear",  params := [], body := .skip })
  , ("plain",                     { name := "plain",                  params := [], body := .skip }) ]

private def ix : ResolveIndex := ResolveIndex.build tbl
private def cx : Ctx := { dialect := .python, table := tbl }

-- Unique suffix: resolvable as a free call, and agrees with `Ctx.resolvable`.
#guard ix.resolvable .python false "helper" == cx.resolvable false "helper"
#guard ix.resolvable .python false "helper" == true
-- Ambiguous suffix (`A.clear` and `B.clear`): `Ctx.resolve` returns `none`, so the free
-- path must say `false`. An index that counted "at least one" would say `true` here and
-- inflate the verifiable core — this is the case that makes the check non-vacuous.
#guard ix.resolvable .python false "clear" == cx.resolvable false "clear"
#guard ix.resolvable .python false "clear" == false
-- The same name on the *method* path is resolvable, because `resolveMethod` takes the
-- first match. The two paths must disagree here; an index collapsing them fails.
#guard ix.resolvable .python true "clear" == cx.resolvable true "clear"
#guard ix.resolvable .python true "clear" == true
-- Exact key with no dot at all.
#guard ix.resolvable .python false "plain" == cx.resolvable false "plain"
#guard ix.resolvable .python false "plain" == true
-- A substring that is not a dotted tail: `"lper"` must not match `".helper"`.
#guard ix.resolvable .python false "lper" == cx.resolvable false "lper"
#guard ix.resolvable .python false "lper" == false
#guard ix.resolvable .python true "lper" == cx.resolvable true "lper"
-- A modelled builtin is resolvable on the free path even though it is not in the table.
#guard ix.resolvable .python false "len" == cx.resolvable false "len"
-- The tail decomposition itself.
#guard dottedTails "m.py:<module>.A.clear" == ["py:<module>.A.clear", "A.clear", "clear"]
#guard dottedTails "plain" == []

-- Conditional verifiability: a holed function whose calls resolve is counted; a holed
-- function with an unresolvable call is not; a hole-free one is in the core instead, and
-- never in both lists.
private def condProg : Program :=
  { funcs :=
    [ { name := "m.py:<module>.helper", params := [], body := .skip }
    , { name := "m.py:<module>.holedOk", params := []
      , body := .seq (.hole "op:delete-index") (.expr (.call "helper" [])) }
    , { name := "m.py:<module>.holedBad", params := []
      , body := .seq (.ret (.hole "expr:genExp")) (.expr (.call "nowhere" [])) } ] }
#guard condProg.conditionallyVerifiable.map (·.name) == ["m.py:<module>.holedOk"]
#guard condProg.callClosed.map (·.name) == ["m.py:<module>.helper"]
#guard (condProg.funcs.flatMap Func.holeSites) == [(true, "op:delete-index"), (false, "expr:genExp")]
#guard holeAssumptionId "m.py:<module>.holedOk" 0 "op:delete-index"
  == "H:m.py:<module>.holedOk#0:op:delete-index"

-- Under Python's scoping rules a bare call name is a variable: a unique table suffix no
-- longer makes it resolvable, a local of that name does, and a builtin still does.
private def strictProg : Program :=
  { pyClasses := some []
  , funcs :=
    [ { name := "m.py:<module>.Holder.helper", params := [], body := .skip }
    , { name := "m.py:<module>.viaSuffix", params := [], body := .expr (.call "helper" []) }
    , { name := "m.py:<module>.viaParam", params := ["helper"], body := .expr (.call "helper" []) }
    , { name := "m.py:<module>.viaLocal", params := []
      , body := .seq (.assign "cb" (.lit .unit)) (.expr (.call "cb" [])) }
    , { name := "m.py:<module>.viaBuiltin", params := ["x"], body := .ret (.call "len" [.name "x"]) }
    , { name := "m.py:<module>.viaQualified", params := []
      , body := .expr (.call "m.py:<module>.Holder.helper" []) } ] }
#guard strictProg.callClosureAgrees
#guard strictProg.callClosed.map (·.name) ==
  [ "m.py:<module>.Holder.helper", "m.py:<module>.viaParam", "m.py:<module>.viaLocal"
  , "m.py:<module>.viaBuiltin", "m.py:<module>.viaQualified" ]
-- The same program without a class table keeps the legacy suffix rule: `viaSuffix` is
-- in (a unique `….helper`), `viaLocal` is out (no table entry `cb`).
#guard ({ strictProg with pyClasses := none } : Program).callClosed.map (·.name) ==
  [ "m.py:<module>.Holder.helper", "m.py:<module>.viaSuffix", "m.py:<module>.viaParam"
  , "m.py:<module>.viaBuiltin", "m.py:<module>.viaQualified" ]

end IndexCheck

/-- The names of functions that can be verified unconditionally. -/
def Program.coreNames (p : Program) : List String :=
  p.callClosed.map (·.name)

end Autoform.Core
