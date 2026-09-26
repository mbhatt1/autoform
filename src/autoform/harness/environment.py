"""Environment model, external-function summaries and the assumption vocabulary.

Every abstraction becomes a named assumption. Every callee the program does not
define is classified as exactly one of INLINE, MODELED, UNINTERPRETED,
NONDETERMINISTIC or UNSUPPORTED; nothing is silently stubbed. A proof whose target
reaches an UNSUPPORTED external is reported as MODEL_INCOMPLETE, never PROVED.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

from .cpir import sha256

CLASSES = ('INLINE', 'MODELED', 'UNINTERPRETED', 'NONDETERMINISTIC', 'UNSUPPORTED')
TRUST = ('trusted', 'modeled', 'assumed', 'unsupported')

DEFAULT_ENVIRONMENT = {
    'filesystem': {'semantics': 'not_modeled'},
    'network': {'semantics': 'not_modeled'},
    'time': {'monotonic_clock': 'not_modeled', 'wall_clock': 'not_modeled'},
    'randomness': {'semantics': 'not_modeled'},
    'database': {'semantics': 'not_modeled'},
    'process': {'fork': 'unsupported', 'signals': 'unsupported'},
    'concurrency': {'model': 'single_threaded'},
    'memory': {'model': 'core_heap', 'pointer_provenance': 'reference_identity',
               'integer_model': 'dialect_specific', 'undefined_behavior': 'hole'},
}

# Names that are nondeterministic or effectful in every supported dialect.
NONDETERMINISTIC = re.compile(r'^(random|rand|time|clock|now|urandom|uuid\d?|getpid|input|read|recv)$')
EFFECTFUL = re.compile(r'^(open|write|send|connect|socket|system|popen|exec\w*|fork|remove|unlink|'
                       r'mkdir|rmdir|rename|print|fopen|fwrite|fread|malloc|free|pthread_\w+)$')


def interpreter_builtins(root: Path) -> set:
    """Names the Core interpreter implements, read from the trusted semantics source."""
    names = set()
    for rel in ('Autoform/Lang/Core/Semantics.lean',):
        path = Path(root) / rel
        if path.is_file():
            names |= set(re.findall(r'\|\s*"([A-Za-z_][A-Za-z0-9_]*)"\s*(?:,|=>)', path.read_text()))
    return names


class Environment:
    def __init__(self, root: Path, overrides: dict | None = None):
        overrides = overrides or {}
        self.model = json.loads(json.dumps(DEFAULT_ENVIRONMENT))
        for key, value in (overrides.get('environment') or {}).items():
            self.model[key] = value
        self.builtins = interpreter_builtins(root)
        self.declared = {}
        for entry in overrides.get('externals', []):
            if entry.get('semantics') not in CLASSES:
                raise ValueError(f"external {entry.get('name')!r}: semantics must be one of {CLASSES}")
            self.declared[entry['name']] = dict(entry, source='environment file')
        self.hash = sha256(dict(model=self.model, externals=self.declared,
                                builtins=sorted(self.builtins)))

    @classmethod
    def load(cls, root: Path, path: Path | None):
        return cls(root, json.loads(Path(path).read_text()) if path else None)

    def summary(self, name: str) -> dict:
        if name in self.declared:
            return self.declared[name]
        bare = name.lstrip('.')
        if name.startswith('<operator>') or name.startswith('.') and bare in self.builtins:
            return dict(name=name, semantics='INLINE', trust_class='trusted',
                        source='Core interpreter operator/method semantics')
        if NONDETERMINISTIC.match(bare):
            return dict(name=name, semantics='NONDETERMINISTIC', trust_class='unsupported',
                        source='no environment model for nondeterministic input')
        if EFFECTFUL.match(bare):
            return dict(name=name, semantics='UNSUPPORTED', trust_class='unsupported',
                        source='effect outside the modeled environment')
        if bare in self.builtins:
            return dict(name=name, semantics='MODELED', trust_class='modeled',
                        source='Core interpreter builtin (unsupported argument shapes evaluate to a hole)')
        if name.startswith('.'):
            return dict(name=name, semantics='MODELED', trust_class='modeled',
                        source='dynamic method dispatch inside the Core heap model')
        return dict(name=name, semantics='UNSUPPORTED', trust_class='unsupported',
                    source='no definition in the program and no declared summary')

    # --- assumptions ------------------------------------------------------------
    def assumptions_for(self, program, fn, claim) -> list:
        """Every assumption a verdict about `claim` depends on, as ledger entries."""
        out = [
            dict(id='A_KERNEL', kind='tcb', text='The Lean kernel, the obligation compiler and the '
                 'Core AST printer are correct.'),
            dict(id='A_SEMANTICS', kind='semantics', text='The Core interpreter models the source dialect '
                 'faithfully for the constructs this function uses (differential tests are evidence, not proof).'),
            dict(id='A_FRONTEND', kind='frontend', text='The pinned Joern front end and exporter translated '
                 'the source without mistranslation.'),
            dict(id='A_SINGLE_THREADED', kind='environment', text='Execution is single-threaded; no '
                 'concurrent writer mutates shared state.'),
        ]
        for binding in claim.get('forall', []):
            p = fn.param(binding['param'])
            if p and p.sort == 'any':
                out.append(dict(id=f'A_DOMAIN_{p.id}', kind='input_domain',
                                text=f'Callers pass `{p.name}` as a {binding["domain"]} value '
                                     f'(the source does not declare its type).'))
        for fid in program.closure(fn.id):
            for name in program.externals(fid):
                s = self.summary(name)
                if s['semantics'] == 'INLINE':
                    continue
                aid = 'A_EXT_' + re.sub(r'[^A-Za-z0-9]', '_', name.lstrip('.'))[:40]
                out.append(dict(id=aid, kind='external', text=f"`{name}`: {s['semantics'].lower()} "
                                f"({s['source']})", semantics=s['semantics']))
        for text in claim.get('assumptions', []):
            aid = 'A_CLAIM_' + sha256(text)[7:15]
            out.append(dict(id=aid, kind='claim', text=text))
        seen, unique = set(), []
        for a in out:
            if a['id'] not in seen:
                seen.add(a['id'])
                unique.append(a)
        return unique

    def unsupported_reach(self, program, fn) -> list:
        return sorted({name for fid in program.closure(fn.id) for name in program.externals(fid)
                       if self.summary(name)['semantics'] in ('UNSUPPORTED', 'NONDETERMINISTIC')})
