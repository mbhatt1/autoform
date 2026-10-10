"""Candidate claim generators. Generators propose; they never certify.

`TemplateGenerator` is deterministic and always available. It instantiates the
parameterized templates of the design (outcome safety, relations between inputs
and result, only-if security shapes, ordering between calls, guarded writes).

`LLMGenerator` asks Claude for candidates in the claim grammar, keyed by the entity
IDs CPIR assigned. Its output is parsed and validated exactly like any other input;
a malformed or hallucinated candidate is rejected with a recorded reason.
"""
from __future__ import annotations

import json
import os
import re

from . import claims as C
from .evidence import SECURITY_WORDS

P = lambda pid: {'param': pid}  # noqa: E731
R = {'result': True}
L = lambda v: {'lit': v}  # noqa: E731
op = lambda name, *args: {'op': name, 'args': list(args)}  # noqa: E731
RESULT_TRUE = op('EQ', R, L(True))
ORDERING_FIRST = SECURITY_WORDS
PRIVILEGED = r'(grant|write|save|store|commit|exec|delete|update|set|insert|send|create|issue|open)'


def _domain(fn, p):
    """Pick a quantification domain for a parameter from its sort and the literals it meets."""
    if p.sort in C.DOMAINS:
        return p.sort
    if p.name in {n for br in fn.branches for n in br.params}:
        if any(isinstance(v, str) for v in fn.literals.get('str', [])):
            return 'str' if len(fn.params) == 1 and not fn.literals.get('int') else 'int'
    return 'int'


def _base(fn, doms, category, subtype, prop, pre=(), on_exception='violates', evidence=None, desc=''):
    return dict(scope={'kind': 'function', 'target': fn.id}, category=category, subtype=subtype,
                forall=[{'param': p.id, 'domain': d} for p, d in doms],
                preconditions=list(pre), property=prop, on_exception=on_exception,
                evidence=evidence or [{'type': 'template', 'location': subtype}],
                provenance={'generator': 'template', 'template': subtype}, description=desc)


class TemplateGenerator:
    name = 'template'

    def generate(self, program, fn, ctx) -> list:
        if fn.synthetic:
            return []
        doms = [(p, _domain(fn, p)) for p in fn.params]
        ints = [p for p, d in doms if d == 'int']
        cited = [e for e in ctx['evidence'] if e['type'] in ('guard', 'test', 'invariant_test', 'documentation')]
        security = ctx['security_relevant']
        naming = [e for e in ctx['evidence'] if e['type'] == 'naming']
        out = []
        add = out.append
        # Outcome safety: the interpreter produces a value or a raised exception, never a hole.
        add(_base(fn, doms, 'safety', 'terminates', {'op': 'TERMINATES'}, on_exception='allowed',
                  evidence=cited + [{'type': 'template', 'location': 'terminates'}],
                  desc='evaluation never reaches an unmodeled construct or exhausts fuel'))
        add(_base(fn, doms, 'safety', 'no_exception', {'op': 'RETURNS'}, evidence=cited[:2] or None,
                  desc='no input in the domain raises'))
        rs = fn.return_sort
        bool_result = rs in ('bool', 'any')
        int_result = rs in ('int', 'any')
        ev_sec = (naming + cited) if security else cited
        if bool_result and len(ints) >= 2:
            a, b = ints[0], ints[1]
            for rel in ('EQ', 'NEQ', 'LT', 'LTE'):
                add(_base(fn, doms, 'security' if security else 'functional', f'result_iff_{rel.lower()}',
                          op('IFF', RESULT_TRUE, op(rel, P(a.id), P(b.id))), evidence=ev_sec or None,
                          desc=f'result is true exactly when {a.name} {C.SYMBOL[rel]} {b.name}'))
            # Only-if (one direction): the security-relevant half of an access check.
            add(_base(fn, doms, 'security', 'grant_only_if_eq',
                      op('IMPLIES', RESULT_TRUE, op('EQ', P(a.id), P(b.id))), evidence=ev_sec or None,
                      desc=f'a true result implies {a.name} = {b.name}'))
            add(_base(fn, doms, 'functional', 'grant_if_eq',
                      op('IMPLIES', op('EQ', P(a.id), P(b.id)), RESULT_TRUE), evidence=ev_sec or None,
                      desc=f'{a.name} = {b.name} implies a true result'))
        if bool_result and len(ints) == 1:
            a = ints[0]
            for rel, lit in (('GT', 0), ('GTE', 0), ('EQ', 0)):
                add(_base(fn, doms, 'functional', f'result_iff_{rel.lower()}_{lit}',
                          op('IFF', RESULT_TRUE, op(rel, P(a.id), L(lit))), evidence=cited or None,
                          desc=f'result is true exactly when {a.name} {C.SYMBOL[rel]} {lit}'))
        if bool_result:
            add(_base(fn, doms, 'functional', 'constant_true', RESULT_TRUE,
                      desc='result is always true'))
            add(_base(fn, doms, 'functional', 'constant_false', op('EQ', R, L(False)),
                      desc='result is always false'))
        if int_result and ints and len(ints) == len(fn.params):
            if len(ints) >= 2:
                a, b = ints[0], ints[1]
                for name, term in (('sum', op('ADD', P(a.id), P(b.id))), ('difference', op('SUB', P(a.id), P(b.id))),
                                   ('product', op('MUL', P(a.id), P(b.id)))):
                    add(_base(fn, doms, 'functional', f'result_is_{name}', op('EQ', R, term), evidence=cited or None,
                              desc=f'result is the {name} of {a.name} and {b.name}'))
                add(_base(fn, doms, 'functional', 'result_ge_first', op('GTE', R, P(a.id)),
                          desc=f'result is at least {a.name}'))
            for a in ints[:2]:
                add(_base(fn, doms, 'functional', f'identity_{a.name}', op('EQ', R, P(a.id)),
                          desc=f'result equals {a.name}'))
            add(_base(fn, doms, 'functional', 'nonnegative', op('GTE', R, L(0)),
                      desc='result is never negative'))
        # Guard conditions are not standalone claims; cegis.py offers them as repairs.
        # Structural ordering: a checking call must precede a privileged one.
        names = [c.callee for c in sorted(fn.calls, key=lambda c: c.order)]
        checks = [n for n in dict.fromkeys(names) if ORDERING_FIRST.search(n.lstrip('.'))]
        privileged = [n for n in dict.fromkeys(names) if re.search(PRIVILEGED, n.lstrip('.'), re.I)]
        for first in checks:
            for then in privileged:
                if first != then:
                    add(_base(fn, [], 'security', 'check_before_privileged',
                              {'op': 'BEFORE', 'first': first, 'then': then},
                              evidence=naming or None,
                              desc=f'every call to {then} is preceded by {first}'))
        if fn.writes and checks:
            add(_base(fn, [], 'structural', 'calls_check', {'op': 'CALLS', 'callee': checks[0]},
                      desc=f'{fn.source_name} calls {checks[0]} before mutating state'))
        return out


SYSTEM = """You propose candidate formal specifications for one function. You are not \
determining whether claims are true; a verifier will do that. Generate candidates only.

Every candidate must:
- reference only the provided entity IDs (F_*, V_*); never invent names
- use only the operators of the property grammar below
- cite evidence from the provided context by type and location
- state assumptions explicitly
- avoid tautologies, reflexive equalities and constants that no evidence mentions
- quantify every parameter for behavioral claims

Grammar (JSON): terms {"param": V_id} | {"result": true} | {"lit": int|bool|str} |
{"op": ADD|SUB|MUL|NEG|LEN, "args": [...]}. Formulas {"op": EQ|NEQ|LT|LTE|GT|GTE, "args": [t,t]} |
{"op": AND|OR, "args": [...]} | {"op": NOT, "args": [f]} | {"op": IMPLIES|IFF, "args": [f,f]} |
{"op": RETURNS|THROWS|TERMINATES} | {"op": CALLS|NOT_CALLS, "callee": name} |
{"op": BEFORE, "first": name, "then": name}. A boolean result is written {"op":"EQ","args":[{"result":true},{"lit":true}]}.
"""

LLM_SCHEMA = {
    'type': 'object',
    'properties': {'claims': {'type': 'array', 'items': {
        'type': 'object',
        'properties': {
            'category': {'type': 'string', 'enum': sorted(C.CATEGORIES)},
            'subtype': {'type': 'string'},
            'forall': {'type': 'array', 'items': {'type': 'object', 'properties': {
                'param': {'type': 'string'}, 'domain': {'type': 'string', 'enum': sorted(C.DOMAINS)}},
                'required': ['param', 'domain'], 'additionalProperties': False}},
            'preconditions_json': {'type': 'string', 'description': 'JSON array of formulas'},
            'property_json': {'type': 'string', 'description': 'one formula as JSON'},
            'on_exception': {'type': 'string', 'enum': ['violates', 'allowed']},
            'assumptions': {'type': 'array', 'items': {'type': 'string'}},
            'evidence': {'type': 'array', 'items': {'type': 'object', 'properties': {
                'type': {'type': 'string', 'enum': sorted(C.EVIDENCE_TYPES)},
                'location': {'type': 'string'}}, 'required': ['type', 'location'],
                'additionalProperties': False}},
            'confidence': {'type': 'number'},
            'description': {'type': 'string'}},
        'required': ['category', 'subtype', 'forall', 'preconditions_json', 'property_json', 'on_exception',
                     'assumptions', 'evidence', 'confidence', 'description'],
        'additionalProperties': False}}},
    'required': ['claims'], 'additionalProperties': False}


class LLMGenerator:
    """Claude-backed candidate synthesis. Optional; outside the trusted base."""
    name = 'llm'

    def __init__(self, model: str | None = None, max_claims: int = 12):
        import anthropic  # noqa: F401  (import error means the generator is unavailable)
        self.model = model or os.environ.get('AUTOFORM_GENERATOR_MODEL', 'claude-opus-5')
        self.max_claims = max_claims
        self.client = anthropic.Anthropic()
        self.rejections = []

    def prompt(self, fn, ctx) -> str:
        view = {k: ctx[k] for k in ('target', 'source_name', 'file', 'location', 'params', 'return_sort',
                                     'body', 'doc', 'callers', 'callees', 'externals', 'writes', 'raises',
                                     'evidence')}
        return (f'Function context (entity IDs are authoritative):\n{json.dumps(view, indent=1, default=str)}\n\n'
                f'Propose at most {self.max_claims} candidate claims with scope target {fn.id}.')

    def generate(self, program, fn, ctx) -> list:
        import anthropic
        if fn.synthetic:
            return []
        try:
            response = self.client.messages.create(
                model=self.model, max_tokens=16000, system=SYSTEM,
                messages=[{'role': 'user', 'content': self.prompt(fn, ctx)}],
                output_config={'format': {'type': 'json_schema', 'schema': LLM_SCHEMA}})
        except (anthropic.APIConnectionError, anthropic.APIStatusError) as exc:
            self.rejections.append(dict(function=fn.id, reason=f'generator unavailable: {exc}'))
            return []
        if response.stop_reason in ('refusal', 'max_tokens'):
            self.rejections.append(dict(function=fn.id, reason=f'generator stopped: {response.stop_reason}'))
            return []
        text = next((b.text for b in response.content if b.type == 'text'), '{}')
        out = []
        for raw in json.loads(text).get('claims', []):
            try:
                claim = dict(scope={'kind': 'function', 'target': fn.id}, category=raw['category'],
                             subtype=raw['subtype'], forall=raw['forall'],
                             preconditions=json.loads(raw['preconditions_json'] or '[]'),
                             property=json.loads(raw['property_json']), on_exception=raw['on_exception'],
                             assumptions=raw['assumptions'], evidence=raw['evidence'],
                             confidence=max(0.0, min(1.0, float(raw['confidence']))),
                             description=raw['description'],
                             provenance={'generator': 'llm', 'model_version': self.model,
                                         'request_id': getattr(response, '_request_id', None)})
                out.append(claim)
            except (KeyError, TypeError, ValueError) as exc:
                self.rejections.append(dict(function=fn.id, reason=f'malformed candidate: {exc}'))
        return out


def generators(spec: str) -> list:
    """`template`, `llm`, or `template,llm`. An unavailable LLM is reported, not faked."""
    out, notes = [], []
    for name in [s.strip() for s in spec.split(',') if s.strip()]:
        if name == 'template':
            out.append(TemplateGenerator())
        elif name == 'llm':
            try:
                out.append(LLMGenerator())
            except Exception as exc:  # missing SDK or credentials
                notes.append(f'LLM generator unavailable: {exc}')
        else:
            raise ValueError(f'unknown generator {name!r}')
    return out, notes
