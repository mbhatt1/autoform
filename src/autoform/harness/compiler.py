"""Obligation compiler: claim → Lean 4 over the Core interpreter.

Universal internal form (design §4):   Pre(I) ∧ T_f(S, I, S', O) ⇒ Post(I, O)
with T_f := `runFunc program FUEL "<f>" args`, the definitional interpreter the rest of
autoform already trusts. Three artifacts are generated per claim:

  prop_<c>  : Prop   ∀ params, Pre → match runFunc … with | outcomes => Post
  chk_<c>   : Bool   the same statement, decidable, one point at a time
  dom_<c>   : List   the finite quantification domain for bounded checking

`outOfFuel` and `hole` never satisfy a claim that mentions the result, so a proof also
establishes that evaluation stays inside the modeled fragment. This compiler is in the
trusted base: it is small, total, and its output is re-parsed and kernel-checked.
"""
from __future__ import annotations

import itertools
import json
import re

from . import claims as C
from .cpir import integer_range

LEAN_TYPE = {'int': 'Int', 'bool': 'Bool', 'str': 'String'}
VAL_CTOR = {'int': '.int', 'bool': '.bool', 'str': '.str'}
REL = {'EQ': '=', 'NEQ': '≠', 'LT': '<', 'LTE': '≤', 'GT': '>', 'GTE': '≥'}
MAX_POINTS = 400


def lean_str(s: str) -> str:
    out = ['"']
    for ch in s:
        if ch in '"\\':
            out.append('\\' + ch)
        elif ch == '\n':
            out.append('\\n')
        elif ch == '\t':
            out.append('\\t')
        elif ord(ch) < 0x20 or ord(ch) == 0x7f:
            out.append('\\x%02x' % ord(ch))
        else:
            out.append(ch)
    return ''.join(out) + '"'


def lean_lit(v) -> str:
    if isinstance(v, bool):
        return 'true' if v else 'false'
    if isinstance(v, int):
        return f'({v} : Int)'
    return lean_str(v)


def var_names(fn) -> dict:
    return {p.id: f'x{p.index}_' + re.sub(r'[^A-Za-z0-9]', '_', p.name)[:24] for p in fn.params}


def term(t, names) -> str:
    if 'param' in t:
        return names[t['param']]
    if 'result' in t:
        return 'res'
    if 'lit' in t:
        return lean_lit(t['lit'])
    a = [term(x, names) for x in t['args']]
    return {'ADD': lambda: f'({a[0]} + {a[1]})', 'SUB': lambda: f'({a[0]} - {a[1]})',
            'MUL': lambda: f'({a[0]} * {a[1]})', 'NEG': lambda: f'(-{a[0]})',
            'LEN': lambda: f'(Int.ofNat (String.length {a[0]}))'}[t['op']]()


def formula(f, names, atoms) -> str:
    if 'lit' in f:
        return 'True' if f['lit'] else 'False'
    op = f['op']
    if op in REL:
        return f"({term(f['args'][0], names)} {REL[op]} {term(f['args'][1], names)})"
    if op in C.OUTCOME:
        return 'True' if atoms[op] else 'False'
    parts = [formula(a, names, atoms) for a in f.get('args', [])]
    if op == 'AND':
        return '(' + ' ∧ '.join(parts) + ')'
    if op == 'OR':
        return '(' + ' ∨ '.join(parts) + ')'
    if op == 'NOT':
        return f'(¬ {parts[0]})'
    if op == 'IMPLIES':
        return f'({parts[0]} → {parts[1]})'
    if op == 'IFF':
        return f'({parts[0]} ↔ {parts[1]})'
    raise ValueError(f'{op} has no Lean encoding')


RET = {'RETURNS': True, 'THROWS': False, 'TERMINATES': True}
EXN = {'RETURNS': False, 'THROWS': True, 'TERMINATES': True}
HOLE = {'RETURNS': False, 'THROWS': False, 'TERMINATES': False}


def body(claim, fn, names, fuel, program_const, decidable) -> str:
    """The match over the interpreter outcome. `decidable` wraps each arm in `decide`."""
    wrap = (lambda p: f'decide {p}') if decidable else (lambda p: p)
    const = (lambda b: 'true' if b else 'false') if decidable else (lambda b: 'True' if b else 'False')
    args = ', '.join(f"{VAL_CTOR[b['domain']]} {names[b['param']]}" for b in claim['forall'])
    call = f'runFunc {program_const} {fuel} {lean_str(fn.name)} [{args}]'
    uses_result = C.mentions_result(claim['property'])
    allowed = claim.get('on_exception') == 'allowed'
    arms = []
    if uses_result:
        sort = claim['result_sort']
        arms.append(f"| .val ({VAL_CTOR[sort]} res) => {wrap(formula(claim['property'], names, RET))}")
        arms.append(f"| .val _ => {const(False)}")
        arms.append(f"| .exn _ => {const(allowed)}")
        arms.append(f"| _ => {const(False)}")
    else:
        arms.append(f"| .val _ => {wrap(formula(claim['property'], names, RET))}")
        exn = formula(claim['property'], names, EXN) if allowed or 'THROWS' in C.operators(claim['property']) \
            else 'False'
        arms.append(f"| .exn _ => {wrap(exn) if exn not in ('True', 'False') else const(exn == 'True')}")
        hole = formula(claim['property'], names, HOLE)
        arms.append(f"| _ => {wrap(hole) if hole not in ('True', 'False') else const(hole == 'True')}")
    return f'(match {call} with\n    ' + '\n    '.join(arms) + ')'


def precondition(claim, names, decidable):
    if not claim['preconditions']:
        return None
    pre = ' ∧ '.join(formula(p, names, RET) for p in claim['preconditions'])
    return f'decide ({pre})' if decidable else f'({pre})'


def domain(claim, fn, program, extra=()) -> list:
    """Finite quantification domain: small values, program literals, width boundaries."""
    lits = [v for vals in fn.literals.values() for v in vals] + list(extra)
    per = []
    for b in claim['forall']:
        p = fn.param(b['param'])
        vals = C.sample_values(b['domain'], lits)
        if b['domain'] == 'int':
            for v in [x for x in lits if type(x) is int][:4]:
                for w in (v - 1, v + 1):
                    if w not in vals:
                        vals.append(w)
            bounds = integer_range(p.integer_type)
            if bounds:
                lo, hi = bounds
                vals = [v for v in vals + [lo, hi, lo + 1, hi - 1] if lo <= v <= hi]
        per.append(list(dict.fromkeys(vals)))
    # Shrink the widest dimensions until the grid fits the budget.
    while per and _count(per) > MAX_POINTS:
        i = max(range(len(per)), key=lambda k: len(per[k]))
        per[i] = per[i][:-1]
    return [list(point) for point in itertools.product(*per)] if per else [[]]


def _count(per):
    n = 1
    for p in per:
        n *= len(p)
    return n


def tuple_type(claim) -> str:
    types = [LEAN_TYPE[b['domain']] for b in claim['forall']]
    return ' × '.join(types) if types else 'Unit'


def tuple_lit(point) -> str:
    if not point:
        return '()'
    if len(point) == 1:
        return lean_lit(point[0])
    return '(' + ', '.join(lean_lit(v) for v in point) + ')'


def accessors(n) -> list:
    """p.1, p.2.1, p.2.2, … for a right-nested product of arity n."""
    if n == 0:
        return []
    if n == 1:
        return ['p']
    out, prefix = [], 'p'
    for i in range(n - 1):
        out.append(prefix + '.1')
        prefix += '.2'
    out.append(prefix)
    return out


class Obligation:
    """All Lean text for one claim; names are derived from the claim id."""

    def __init__(self, claim, fn, program, module, fuel=1000, extra_values=()):
        self.claim, self.fn = claim, fn
        self.tag = claim['id'].lower()
        self.names = var_names(fn)
        self.program_const = f'Autoform.Generated.{module}.program'
        self.fuel = fuel
        self.points = domain(claim, fn, program, extra_values)
        bind = ' '.join(f"({self.names[b['param']]} : {LEAN_TYPE[b['domain']]})" for b in claim['forall'])
        self.binders = bind
        self.params = [self.names[b['param']] for b in claim['forall']]

    def prop(self) -> str:
        pre = precondition(self.claim, self.names, False)
        core = body(self.claim, self.fn, self.names, self.fuel, self.program_const, False)
        stmt = f'{pre} → {core}' if pre else core
        return f'∀ {self.binders}, {stmt}' if self.binders else stmt

    def check_def(self) -> str:
        pre = precondition(self.claim, self.names, True)
        core = body(self.claim, self.fn, self.names, self.fuel, self.program_const, True)
        expr = f'(!({pre}) || {core})' if pre else core
        return f'def chk_{self.tag} {self.binders} : Bool :=\n  {expr}\n'

    def apply(self, var='p') -> str:
        acc = accessors(len(self.params))
        return f'chk_{self.tag} ' + ' '.join(a.replace('p', var, 1) for a in acc) if acc else f'chk_{self.tag}'

    def apply_point(self, point) -> str:
        return f'chk_{self.tag} ' + ' '.join(lean_lit(v) for v in point) if point else f'chk_{self.tag}'

    def domain_def(self) -> str:
        items = ', '.join(tuple_lit(p) for p in self.points)
        return f'def dom_{self.tag} : List ({tuple_type(self.claim)}) := [{items}]\n'

    def outcome_call(self, point) -> str:
        args = ', '.join(f"{VAL_CTOR[b['domain']]} {lean_lit(v)}" for b, v in zip(self.claim['forall'], point))
        return f'runFunc {self.program_const} {self.fuel} {lean_str(self.fn.name)} [{args}]'

    def search(self) -> str:
        """Compiled evaluation that reports the first failing point (witness candidate only)."""
        acc = accessors(len(self.params))
        js = ' ++ ", " ++ '.join(f'(Lean.toJson {a}).compress' for a in acc) or '""'
        return (f'#eval match (dom_{self.tag}).find? (fun p => !({self.apply()})) with\n'
                f'  | some p => IO.println ("AUTOFORM_CE {self.claim["id"]} [" ++ {js} ++ "]")\n'
                f'  | none => IO.println "AUTOFORM_NOCE {self.claim["id"]}"\n')

    def points_in_pre(self) -> int:
        """How many domain points satisfy the preconditions (vacuity guard for bounded proofs)."""
        if not self.claim['preconditions']:
            return len(self.points)
        n = 0
        for point in self.points:
            env = {b['param']: v for b, v in zip(self.claim['forall'], point)}
            try:
                if all(C.eval_formula(p, env) for p in self.claim['preconditions']):
                    n += 1
            except (C.Undefined, TypeError):
                n += 1
        return n


SYMBOLIC_EVAL = r'''
open Lean Meta in
/-- Head-normalize an interpreter application by unfolding and iota-reduction only. -/
partial def afHead (e : Lean.Expr) (fuel : Nat) : MetaM Lean.Expr := do
  if fuel == 0 then return e
  let e ← whnfCore e
  if let .const n _ := e.getAppFn then
    if (← getEnv).find? n matches some (.ctorInfo _) then return e
  match ← unfoldDefinition? e with
  | some e' => afHead e' (fuel - 1)
  | none => return e

open Lean Elab Tactic Meta in
/-- Symbolic evaluation: replace each `runFunc …` in the goal by its head-normal form.
The replacement is a `change`, so the kernel re-checks it by definitional equality;
this tactic cannot make a false goal provable. -/
elab "af_eval" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← withTransparency .all <| Meta.transform t (pre := fun e => do
    if e.isAppOf ``Autoform.Core.runFunc then
      return .done (← afHead e 200000)
    return .continue)
  replaceMainGoal [← withTransparency .all <| g.change t']
'''

UNIVERSAL_TACTIC = ('intros\n  af_eval\n  first | trivial | simp | simp [Val.beq] | decide | omega '
                    '| (simp; omega) | (simp [Val.beq]; omega) | simp_all [Val.beq]')
DEEP_TACTIC = 'intros\n  first | decide +kernel | portfolio'


def header(module) -> str:
    return (f'import Autoform.Generated.{module}\nimport Autoform.Tactics.Portfolio\nimport Lean.Data.Json\n'
            'set_option autoImplicit false\nset_option maxRecDepth 100000\n'
            'set_option maxHeartbeats 4000000\nset_option linter.all false\nset_option maxErrors 100000\n'
            'open Autoform.Core\n' + SYMBOLIC_EVAL)


def witness_json(point) -> str:
    return json.dumps(point)
