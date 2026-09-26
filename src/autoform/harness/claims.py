"""Claim language: a deliberately small, typed DSL over CPIR entity identifiers.

A claim is data, never prose. Generators (templates or an LLM) emit JSON in this
grammar; `validate` rejects anything that names an entity CPIR does not contain,
mixes sorts, or uses an operator outside the grammar. Nothing here decides truth.

Term forms
    {"param": "V_0003"}                 a quantified parameter of the target
    {"result": true}                    the target's return value
    {"lit": 3} | {"lit": true} | {"lit": "admin"}
    {"op": "ADD"|"SUB"|"MUL"|"NEG"|"LEN", "args": [...]}

Formula forms
    {"op": "EQ"|"NEQ"|"LT"|"LTE"|"GT"|"GTE", "args": [t, t]}
    {"op": "AND"|"OR", "args": [...]}, {"op": "NOT", "args": [f]}
    {"op": "IMPLIES"|"IFF", "args": [f, f]}
    {"op": "RETURNS"} | {"op": "THROWS"} | {"op": "TERMINATES"}     outcome of the call
    {"op": "CALLS", "callee": NAME} | {"op": "NOT_CALLS", "callee": NAME}
    {"op": "BEFORE", "first": NAME, "then": NAME}                    every `then` call is preceded by `first`
    {"op": "WRITES", "target": NAME} | {"op": "NO_WRITE", "target": NAME}

Reserved (parsed, typed as formulas, verified only by backends that support them):
    ALWAYS EVENTUALLY UNTIL NEXT FLOWS_TO NO_FLOW TAINTED SANITIZED AUTHORIZED
    AUTHENTICATED CONFIDENTIAL INTEGRITY_PROTECTED OPEN CLOSED OWNED RELEASED BALANCED
    READS ALLOCATES FREES LOCKS UNLOCKS REACHES DOMINATES POSTDOMINATES
"""
from __future__ import annotations

import copy
import hashlib
import itertools
import json

COMPARE = {'EQ', 'NEQ', 'LT', 'LTE', 'GT', 'GTE'}
ORDER = {'LT', 'LTE', 'GT', 'GTE'}
BOOLEAN = {'AND', 'OR', 'NOT', 'IMPLIES', 'IFF'}
ARITH = {'ADD': 2, 'SUB': 2, 'MUL': 2, 'NEG': 1, 'LEN': 1}
OUTCOME = {'RETURNS', 'THROWS', 'TERMINATES'}
STRUCTURAL = {'CALLS', 'NOT_CALLS', 'BEFORE', 'WRITES', 'NO_WRITE'}
RESERVED = {'ALWAYS', 'EVENTUALLY', 'UNTIL', 'NEXT', 'FLOWS_TO', 'NO_FLOW', 'TAINTED', 'SANITIZED',
            'AUTHORIZED', 'AUTHENTICATED', 'CONFIDENTIAL', 'INTEGRITY_PROTECTED', 'OPEN', 'CLOSED',
            'OWNED', 'RELEASED', 'BALANCED', 'READS', 'ALLOCATES', 'FREES', 'LOCKS', 'UNLOCKS',
            'REACHES', 'DOMINATES', 'POSTDOMINATES', 'ONLY_IF'}
COMMUTATIVE = {'AND', 'OR', 'EQ', 'NEQ', 'IFF', 'ADD', 'MUL'}
CATEGORIES = {'functional', 'safety', 'security', 'resource', 'temporal', 'structural'}
DOMAINS = {'int', 'bool', 'str'}
EVIDENCE_TYPES = {'assertion', 'test', 'invariant_test', 'api_contract', 'documentation', 'caller',
                  'comment', 'naming', 'runtime_trace', 'guard', 'template', 'counterexample'}
CLAIM_KEYS = {'id', 'scope', 'category', 'subtype', 'forall', 'preconditions', 'property',
              'assumptions', 'evidence', 'provenance', 'confidence', 'status', 'on_exception',
              'description', 'parent'}
# Evidence ordering from the design: explicit assertion > invariant test > API contract >
# caller assumption > comment > naming inference.
EVIDENCE_WEIGHT = {'assertion': 1.0, 'guard': 0.9, 'invariant_test': 0.85, 'test': 0.8,
                   'runtime_trace': 0.7, 'api_contract': 0.7, 'caller': 0.55, 'documentation': 0.5,
                   'comment': 0.35, 'naming': 0.2, 'template': 0.15, 'counterexample': 0.6}


class ClaimError(ValueError):
    pass


# --- validation ---------------------------------------------------------------

def _term_sort(t, env, result_sort):
    if not isinstance(t, dict):
        raise ClaimError('term must be an object')
    if 'param' in t:
        if t['param'] not in env:
            raise ClaimError(f"unknown or unquantified parameter {t['param']!r}")
        return env[t['param']]
    if 'result' in t:
        return result_sort.setdefault('sort', None) or 'result?'
    if 'lit' in t:
        v = t['lit']
        if isinstance(v, bool):
            return 'bool'
        if isinstance(v, int):
            return 'int'
        if isinstance(v, str):
            return 'str'
        raise ClaimError('literals must be int, bool or str')
    op = t.get('op')
    if op in ARITH:
        args = t.get('args')
        if not isinstance(args, list) or len(args) != ARITH[op]:
            raise ClaimError(f'{op} takes {ARITH[op]} arguments')
        if op == 'LEN':
            _unify(_term_sort(args[0], env, result_sort), 'str', args[0], result_sort)
            return 'int'
        for a in args:
            _unify(_term_sort(a, env, result_sort), 'int', a, result_sort)
        return 'int'
    raise ClaimError(f'not a term: {json.dumps(t)[:80]}')


def _unify(found, wanted, term, result_sort):
    if found == 'result?':
        if result_sort.get('sort') not in (None, wanted):
            raise ClaimError('result used at two different sorts')
        result_sort['sort'] = wanted
        return wanted
    if wanted == 'result?':
        return found
    if found != wanted:
        raise ClaimError(f'sort mismatch: {found} where {wanted} is required')
    return found


def _formula(f, env, result_sort, program, fn):
    if not isinstance(f, dict) or not isinstance(f.get('op'), str):
        raise ClaimError('formula must be an object with an op')
    op = f['op']
    extra = set(f) - {'op', 'args', 'callee', 'first', 'then', 'target'}
    if extra:
        raise ClaimError(f'unknown formula fields {sorted(extra)}')
    if op in COMPARE:
        a, b = _args(f, 2)
        sa, sb = _term_sort(a, env, result_sort), _term_sort(b, env, result_sort)
        if sa == 'result?' and sb == 'result?':
            raise ClaimError('comparison of result with itself is reflexive')
        if sa == 'result?':
            sort = _unify(sa, sb, a, result_sort)
        elif sb == 'result?':
            sort = _unify(sb, sa, b, result_sort)
        else:
            sort = _unify(sa, sb, a, result_sort)
        if op in ORDER and sort != 'int':
            raise ClaimError(f'{op} needs int arguments')
        return
    if op in BOOLEAN:
        args = f.get('args')
        need = {'NOT': 1, 'IMPLIES': 2, 'IFF': 2}.get(op)
        if not isinstance(args, list) or (need and len(args) != need) or (not need and len(args) < 2):
            raise ClaimError(f'bad arity for {op}')
        for a in args:
            if isinstance(a, dict) and 'lit' in a and isinstance(a['lit'], bool):
                continue
            _formula(a, env, result_sort, program, fn)
        return
    if op in OUTCOME:
        if f.get('args'):
            raise ClaimError(f'{op} takes no arguments')
        return
    if op in STRUCTURAL:
        keys = {'BEFORE': ('first', 'then'), 'WRITES': ('target',), 'NO_WRITE': ('target',)}.get(op, ('callee',))
        for key in keys:
            if not isinstance(f.get(key), str) or not f[key]:
                raise ClaimError(f'{op} requires {key}')
        known = {c.callee for c in fn.calls} | {w['target'] for w in fn.writes}
        # A structural claim about something the function never mentions is only
        # meaningful for negative forms (NOT_CALLS / NO_WRITE), which stay allowed.
        if op in ('CALLS', 'BEFORE', 'WRITES'):
            for key in keys:
                if f[key] not in known:
                    raise ClaimError(f'{op} names {f[key]!r}, which {fn.name} never mentions')
        return
    if op in RESERVED:
        return
    raise ClaimError(f'operator {op!r} is outside the claim grammar')


def _args(f, n):
    args = f.get('args')
    if not isinstance(args, list) or len(args) != n:
        raise ClaimError(f"{f.get('op')} takes {n} arguments")
    return args


def validate(claim: dict, program) -> dict:
    """Return a normalized claim or raise ClaimError. Pure; never consults a model."""
    if not isinstance(claim, dict):
        raise ClaimError('claim must be an object')
    unknown = set(claim) - CLAIM_KEYS
    if unknown:
        raise ClaimError(f'unknown claim fields {sorted(unknown)}')
    scope = claim.get('scope')
    if not isinstance(scope, dict) or scope.get('kind') != 'function' or scope.get('target') not in program.by_id:
        raise ClaimError('scope must be {"kind": "function", "target": <existing F_ id>}')
    fn = program.by_id[scope['target']]
    category = claim.get('category', 'functional')
    if category not in CATEGORIES:
        raise ClaimError(f'category must be one of {sorted(CATEGORIES)}')
    forall = claim.get('forall', [])
    if not isinstance(forall, list):
        raise ClaimError('forall must be a list')
    env = {}
    for binding in forall:
        if not isinstance(binding, dict) or set(binding) != {'param', 'domain'}:
            raise ClaimError('forall entries are {"param": V_id, "domain": int|bool|str}')
        p = fn.param(binding['param'])
        if p is None:
            raise ClaimError(f"{binding['param']!r} is not a parameter of {fn.id}")
        if binding['domain'] not in DOMAINS:
            raise ClaimError('domain must be int, bool or str')
        if p.sort not in ('any', binding['domain']):
            raise ClaimError(f'{p.id} has sort {p.sort}, not {binding["domain"]}')
        if p.id in env:
            raise ClaimError(f'{p.id} quantified twice')
        env[p.id] = binding['domain']
    structural = _is_structural(claim.get('property'))
    if not structural and set(env) != {p.id for p in fn.params}:
        raise ClaimError('behavioral claims must quantify every parameter of the target')
    result_sort = {}
    for pre in claim.get('preconditions', []):
        if _mentions_result(pre):
            raise ClaimError('preconditions may not mention the result')
        _formula(pre, env, result_sort, program, fn)
    if 'property' not in claim:
        raise ClaimError('claim requires a property')
    _formula(claim['property'], env, result_sort, program, fn)
    if _mentions_result(claim['property']) and result_sort.get('sort') is None:
        raise ClaimError('result sort cannot be inferred')
    if fn.return_sort not in ('any', result_sort.get('sort') or fn.return_sort):
        raise ClaimError(f'{fn.name} returns {fn.return_sort}, not {result_sort["sort"]}')
    for key in ('assumptions',):
        if not all(isinstance(a, str) and a for a in claim.get(key, [])):
            raise ClaimError('assumptions are nonempty strings')
    for ev in claim.get('evidence', []):
        if not isinstance(ev, dict) or ev.get('type') not in EVIDENCE_TYPES:
            raise ClaimError(f'evidence types are {sorted(EVIDENCE_TYPES)}')
    conf = claim.get('confidence', 0.0)
    if not isinstance(conf, (int, float)) or not 0 <= conf <= 1:
        raise ClaimError('confidence must be in [0, 1]')
    if claim.get('on_exception', 'violates') not in ('violates', 'allowed'):
        raise ClaimError('on_exception is violates or allowed')
    out = copy.deepcopy(claim)
    out['category'] = category
    out.setdefault('subtype', category)
    out.setdefault('forall', [])
    out.setdefault('preconditions', [])
    out.setdefault('assumptions', [])
    out.setdefault('evidence', [])
    out.setdefault('on_exception', 'violates')
    out['result_sort'] = result_sort.get('sort')
    out['structural'] = structural
    out['preconditions'] = [canonical(p) for p in out['preconditions']]
    out['property'] = canonical(out['property'])
    out['id'] = claim_id(out, program)
    out.setdefault('status', 'candidate')
    return out


def _is_structural(f):
    return isinstance(f, dict) and f.get('op') in STRUCTURAL or (
        isinstance(f, dict) and f.get('op') in ('AND', 'OR', 'NOT')
        and all(_is_structural(a) for a in f.get('args', [])))


def _mentions_result(f):
    if isinstance(f, dict):
        return 'result' in f or any(_mentions_result(v) for k, v in f.items() if k != 'op')
    if isinstance(f, list):
        return any(_mentions_result(v) for v in f)
    return False


def mentions_result(f):
    return _mentions_result(f)


def operators(f, found=None):
    found = set() if found is None else found
    if isinstance(f, dict):
        if isinstance(f.get('op'), str):
            found.add(f['op'])
        for k, v in f.items():
            if k != 'op':
                operators(v, found)
    elif isinstance(f, list):
        for v in f:
            operators(v, found)
    return found


# --- canonical form, identity, complexity ------------------------------------

def canonical(f):
    if not isinstance(f, dict) or 'op' not in f:
        return f
    g = dict(f)
    if 'args' in g:
        args = [canonical(a) for a in g['args']]
        if g['op'] in ('AND', 'OR'):
            flat = []
            for a in args:
                flat += a['args'] if isinstance(a, dict) and a.get('op') == g['op'] else [a]
            args = []
            for a in flat:
                if a not in args:
                    args.append(a)
        if g['op'] in COMMUTATIVE:
            args = sorted(args, key=lambda a: json.dumps(a, sort_keys=True))
        g['args'] = args
    return g


def _named(value, names):
    if isinstance(value, dict):
        return {k: (names.get(v, v) if k in ('param', 'target') and isinstance(v, str) else _named(v, names))
                for k, v in value.items()}
    if isinstance(value, list):
        return [_named(v, names) for v in value]
    return value


def claim_id(claim, program) -> str:
    """Stable across revisions: hashes qualified names, never positional CPIR ids."""
    fn = program.by_id[claim['scope']['target']]
    names = {fn.id: 'fn:' + fn.name, **{p.id: 'param:' + p.name for p in fn.params}}
    claim = _named({k: claim.get(k) for k in ('scope', 'forall', 'preconditions', 'property',
                                              'on_exception', 'assumptions')}, names)
    core = dict(scope=claim['scope'], forall=sorted(claim.get('forall') or [], key=lambda b: b['param']),
                pre=sorted((json.dumps(p, sort_keys=True) for p in claim.get('preconditions', []))),
                prop=claim['property'], exc=claim.get('on_exception', 'violates'),
                assumptions=sorted(claim.get('assumptions', [])))
    return 'C_' + hashlib.sha256(json.dumps(core, sort_keys=True).encode()).hexdigest()[:10]


def size(f) -> int:
    if isinstance(f, dict):
        return 1 + sum(size(v) for k, v in f.items() if k not in ('op',) and isinstance(v, (dict, list)))
    if isinstance(f, list):
        return sum(size(v) for v in f)
    return 0


def complexity(claim) -> int:
    return (size(claim['property']) + sum(size(p) for p in claim.get('preconditions', []))
            + 2 * len(claim.get('assumptions', [])))


def evidence_score(claim) -> float:
    """E(c) = Σ w_type, saturating; independent source types count, repeats do not."""
    types = {e['type'] for e in claim.get('evidence', [])}
    total = 1.0
    for t in types:
        total *= 1 - EVIDENCE_WEIGHT.get(t, 0.1)
    return round(1 - total, 3)


def independent_sources(claim) -> int:
    # Templates, names and our own counterexamples say nothing independent about intent.
    return len({e['type'] for e in claim.get('evidence', [])
                if e['type'] not in ('template', 'naming', 'counterexample')})


# --- local evaluation (critic only; never evidence of truth about the program) ---

class Undefined(Exception):
    pass


def eval_term(t, env):
    if 'param' in t:
        return env[t['param']]
    if 'result' in t:
        if 'result' not in env:
            raise Undefined
        return env['result']
    if 'lit' in t:
        return t['lit']
    a = [eval_term(x, env) for x in t['args']]
    op = t['op']
    if op == 'ADD':
        return a[0] + a[1]
    if op == 'SUB':
        return a[0] - a[1]
    if op == 'MUL':
        return a[0] * a[1]
    if op == 'NEG':
        return -a[0]
    if op == 'LEN':
        return len(a[0])
    raise Undefined


def eval_formula(f, env) -> bool:
    if 'lit' in f:
        return bool(f['lit'])
    op = f['op']
    if op in COMPARE:
        x, y = (eval_term(a, env) for a in f['args'])
        return {'EQ': x == y, 'NEQ': x != y, 'LT': x < y, 'LTE': x <= y, 'GT': x > y, 'GTE': x >= y}[op]
    if op == 'AND':
        return all(eval_formula(a, env) for a in f['args'])
    if op == 'OR':
        return any(eval_formula(a, env) for a in f['args'])
    if op == 'NOT':
        return not eval_formula(f['args'][0], env)
    if op == 'IMPLIES':
        return (not eval_formula(f['args'][0], env)) or eval_formula(f['args'][1], env)
    if op == 'IFF':
        return eval_formula(f['args'][0], env) == eval_formula(f['args'][1], env)
    if op in OUTCOME:
        return env.get('outcome:' + op, True)
    raise Undefined


def sample_values(domain, literals=()):
    base = {'int': [-2, -1, 0, 1, 2, 3], 'bool': [False, True], 'str': ['', 'a', 'admin']}[domain]
    extra = [v for v in literals if (domain == 'int' and type(v) is int) or
             (domain == 'str' and isinstance(v, str)) or (domain == 'bool' and isinstance(v, bool))]
    out = []
    for v in base + extra[:4]:
        if v not in out:
            out.append(v)
    return out


def assignments(claim, literals=(), limit=4096):
    domains = [(b['param'], sample_values(b['domain'], literals)) for b in claim.get('forall', [])]
    count = 0
    for combo in itertools.product(*[vals for _, vals in domains]):
        yield {pid: v for (pid, _), v in zip(domains, combo)}
        count += 1
        if count >= limit:
            return


# --- rendering ----------------------------------------------------------------

SYMBOL = {'EQ': '=', 'NEQ': '≠', 'LT': '<', 'LTE': '≤', 'GT': '>', 'GTE': '≥', 'ADD': '+', 'SUB': '-',
          'MUL': '*', 'AND': '∧', 'OR': '∨', 'IMPLIES': '→', 'IFF': '↔'}


def render(f, names) -> str:
    if 'param' in f:
        return names.get(f['param'], f['param'])
    if 'result' in f:
        return 'result'
    if 'lit' in f:
        return json.dumps(f['lit'])
    op = f['op']
    if op in OUTCOME:
        return op.lower()
    if op in STRUCTURAL or op in RESERVED:
        fields = [f[k] for k in ('callee', 'first', 'then', 'target') if k in f]
        return f"{op}({', '.join(fields + [render(a, names) for a in f.get('args', [])])})"
    args = [render(a, names) for a in f['args']]
    if op == 'NOT':
        return f'¬({args[0]})'
    if op == 'NEG':
        return f'-({args[0]})'
    if op == 'LEN':
        return f'len({args[0]})'
    return '(' + f' {SYMBOL[op]} '.join(args) + ')'


def render_claim(claim, program) -> str:
    fn = program.by_id[claim['scope']['target']]
    names = {p.id: p.name for p in fn.params}
    q = ' '.join(f"{names[b['param']]}:{b['domain']}" for b in claim['forall'])
    body = render(claim['property'], names)
    if claim['preconditions']:
        body = ' ∧ '.join(render(p, names) for p in claim['preconditions']) + ' ⇒ ' + body
    head = f'∀ {q}. ' if q else ''
    tail = '' if claim.get('on_exception') == 'violates' else ' (exceptions allowed)'
    return f'{fn.source_name or fn.name}: {head}{body}{tail}'
