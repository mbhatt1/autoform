"""L1 step: prove an AI-written model equal to the deep translation of the same function.

A function qualifies when it has BOTH a validated `LeanModel` (level L0: it agreed with the
real code on every tested input and with an independent second translation) and a deep
(Joern → Core) translation that is hole-free and call-closed. For each argument shape the
model is used at — the model's signature, plus every binder shape a statement about it
uses — the step states

    theorem l1_<f> : ∀ (a : Int) (b : Int),
        <model call_template "<model name>" [.int a, .int b]>
          = <deep call_template "<deep name>" [.int a, .int b]>

(the deep side is the deep translation's `call_template`, so a function that runs from an
initialized heap uses that entry) and sends it to the prover agent
(`autoform.harness.prover`, the same machinery as the prove stage: the proof is spliced
under the original statement, screened, re-elaborated, and its axioms checked).

Before any agent call a cheap bounded check runs: over the check stage's domain for the
shape, `decide +kernel` must accept that the two sides agree on every point where their
results are comparable (int/bool/str/None results and exceptions named by a string). A
point where they differ (found by compiled evaluation) skips the L1 attempt: the model and
the deep translation disagree, so the equality is false. The bounded check is a filter,
never evidence for L1.

If every shape is proved, the model's level becomes L1: every statement proved about the
model at a proved shape is, by rewriting with `l1_<f>`, a statement about the deep
translation. Otherwise the model stays at L0 and the reason is recorded. Nothing here
modifies models.json; the report combines `refine.json` with it.
"""
from __future__ import annotations

import os
import re
from dataclasses import asdict, dataclass, field
from pathlib import Path

from ..harness.compiler import accessors, lean_str
from . import check as nl_check
from .schema import FILES, dump

DEFAULT_CACHE = Path(os.environ.get('AUTOFORM_PROOF_CACHE', Path.home() / '.cache/autoform/proofs'))
LEAN_TIMEOUT = 900
KINDS = {'Int': 'int', 'ℤ': 'int', 'Nat': 'nat', 'ℕ': 'nat', 'Bool': 'bool', 'String': 'str'}
TYPE_OF = {'int': 'Int', 'nat': 'Nat', 'bool': 'Bool', 'str': 'String'}
VAL_OF = {'int': '.int {x}', 'nat': '.int ({x} : Int)', 'bool': '.bool {x}', 'str': '.str {x}'}
LEAN_KEYWORDS = {'fun', 'let', 'in', 'have', 'show', 'from', 'by', 'do', 'then', 'else', 'if', 'match', 'with',
                 'at', 'end', 'open', 'where', 'def', 'theorem', 'forall', 'exists', 'Type', 'Prop', 'Sort'}

# Structural comparison on the result shapes with an unambiguous meaning; `none` when
# the two results are not comparable this way (floats, containers, objects, ...).
L1EQ = '''
def l1eq : EResult → EResult → Option Bool
  | .val (.int x), .val (.int y) => some (x == y)
  | .val (.bool x), .val (.bool y) => some (x == y)
  | .val (.str x), .val (.str y) => some (x == y)
  | .val .unit, .val .unit => some true
  | .exn (.str x), .exn (.str y) => some (x == y)
  | .val _, .val _ => none
  | .exn _, .exn _ => none
  | .hole _, .hole _ => none
  | .outOfFuel, .outOfFuel => some true
  | _, _ => some false
'''


@dataclass
class L1Result:
    function: str                  # model FunctionInfo.name
    deep_function: str | None
    status: str                    # PROVED | FAILED | DISAGREES | SKIPPED
    level: str                     # resulting level: L1 | L0 | none
    shapes: list = field(default_factory=list)   # [{kinds, theorem, statement, bounded, proof...}]
    reason: str = ''
    cost_usd: float = 0.0


def _d(x) -> dict:
    return asdict(x) if hasattr(x, '__dataclass_fields__') else dict(x or {})


def split_arrows(sig: str) -> list:
    """Top-level `→` components of a Lean type."""
    parts, depth, cur = [], 0, ''
    i = 0
    while i < len(sig):
        ch = sig[i]
        depth += ch in '([{'
        depth -= ch in ')]}'
        if depth == 0 and (sig.startswith('→', i) or sig.startswith('->', i)):
            parts.append(cur.strip())
            cur = ''
            i += 1 if sig[i] == '→' else 2
            continue
        cur += ch
        i += 1
    parts.append(cur.strip())
    return [p for p in parts if p]


def signature_shape(sig: str) -> tuple | None:
    """Argument kinds of a plain def's type, e.g. 'Int → Int → Int' → ('int', 'int');
    None when an argument type has no `Val` encoding here."""
    parts = split_arrows(sig or '')
    if not parts:
        return None
    kinds = []
    for p in parts[:-1]:
        m = re.fullmatch(r'[({]\s*([\w\s\']+?)\s*:\s*(.+?)\s*[)}]', p)
        if m:
            names, ty = m.group(1).split(), m.group(2)
        else:
            names, ty = [None], p
        kind = KINDS.get(ty.strip())
        if kind is None:
            return None
        kinds += [kind] * len(names)
    return tuple(kinds)


def statement_shape(st: dict) -> tuple | None:
    """Argument kinds of a statement's binders when each is passed as `.int x`/`.bool x`/`.str x`."""
    kinds = []
    for b in st.get('binders') or []:
        m = nl_check.VAL_RE.match(str(b.get('val', '')))
        kind = KINDS.get(str(b.get('type', '')).strip())
        if not m or kind not in ('int', 'bool', 'str') or m.group(1) != kind or m.group(2) != b.get('name'):
            return None
        kinds.append(kind)
    return tuple(kinds)


def binder_names(fn: dict, n: int) -> list:
    names = []
    for i in range(n):
        params = fn.get('params') or []
        p = params[i].get('name') if i < len(params) and isinstance(params[i], dict) else None
        ok = p and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', p) and p not in LEAN_KEYWORDS and p not in names
        names.append(p if ok else f'x{i + 1}')
    return names


def entry_modules(translation: dict) -> list:
    """Lean modules a translation's call_template names (`Autoform.NLModel.<M>` for an AI
    model, `Autoform.NL.<M>` for a deep translation's initialized entry)."""
    tmpl = translation.get('call_template', '')
    return list(dict.fromkeys(re.findall(r'\b(Autoform\.(?:NLModel|NL)\.[A-Za-z0-9_]+)\.call[FH]?\b', tmpl)))


def module_of(translation: dict) -> str | None:
    """The Lean module a translation's call_template refers to."""
    mods = entry_modules(translation)
    if mods:
        return mods[0]
    m = re.search(r'(Autoform\.Generated\.[\w]+)\.', translation.get('call_template', ''))
    if m:
        return m.group(1)
    return f"Autoform.Generated.{translation['module']}" if translation.get('module') else None


def header(model_tr: dict, deep_tr: dict) -> str:
    """Imports the model module, the deep module (and its initialized entry, if the deep
    call_template uses one), the af_eval tactic, `open Autoform.Core`."""
    from ..harness import compiler
    mods = entry_modules(model_tr) + [m for m in entry_modules(deep_tr) if m not in entry_modules(model_tr)]
    return ''.join(f'import {m}\n' for m in mods) + compiler.header(deep_tr['module'])


def call(template: str, name: str, vals: list) -> str:
    return template.replace('{name}', lean_str(name)).replace('{args}', '[' + ', '.join(vals) + ']')


def sanitize(name: str) -> str:
    s = re.sub(r'[^A-Za-z0-9_]', '_', name).strip('_') or 'f'
    return s if s[0].isalpha() else 'f_' + s


def pair(model_fn: dict, deep_fns: list) -> dict | None:
    """The deep FunctionInfo for a model function: same qualified name, else same file and name."""
    for f in deep_fns:
        if f.get('name') == model_fn.get('name'):
            return f
    cands = [f for f in deep_fns if f.get('source_name') == model_fn.get('source_name')
             and (f.get('file') == model_fn.get('file') or not model_fn.get('file'))]
    return cands[0] if len(cands) == 1 else None


class Shape:
    """One argument shape of one function: the L1 statement and its bounded filter."""

    def __init__(self, idx: int, kinds: tuple, model_fn: dict, deep_fn: dict, model_tr: dict, deep_tr: dict,
                 model: dict, cap: int, multi: bool, used: set):
        self.kinds = tuple(kinds)
        self.names = binder_names(model_fn, len(kinds))
        self.types = [TYPE_OF[k] for k in kinds]
        vals = [VAL_OF[k].format(x=n) for k, n in zip(kinds, self.names)]
        self.lhs = call(model_tr['call_template'], model_fn['name'], vals)
        self.rhs = call(deep_tr['call_template'], deep_fn['name'], vals)
        base = 'l1_' + sanitize(model_fn.get('source_name') or model_fn['name'])
        self.theorem = base + (f'_{idx}' if multi else '')
        while self.theorem in used:
            self.theorem += '_'
        used.add(self.theorem)
        self.tag = f'{self.theorem}__{idx}'
        sig = ' '.join(f'({n} : {t})' for n, t in zip(self.names, self.types))
        self.statement = (f'theorem {self.theorem} : ∀ {sig}, {self.lhs} = {self.rhs}' if kinds
                          else f'theorem {self.theorem} : {self.lhs} = {self.rhs}')
        self.sig = sig
        binders = [{'name': n, 'type': t} for n, t in zip(self.names, self.types)]
        _, self.points = nl_check.domain(binders, deep_fn, deep_tr.get('language', ''), cap)
        self.model_fn, self.deep_fn, self.model = model_fn, deep_fn, model

    def bounded_block(self) -> str:
        t = self.tag
        items = ', '.join(nl_check.tuple_lit(self.kinds, p) for p in self.points)
        args = ' '.join(accessors(len(self.names)))
        sig = self.sig
        agree = f'(l1eq ({self.lhs}) ({self.rhs}))'
        return '\n'.join([
            f'def l1dom_{t} : List ({nl_check.tuple_type(self.kinds)}) := [{items}]',
            f'def l1agree_{t} {sig} : Bool := {agree}.getD true',
            f'def l1cmp_{t} {sig} : Bool := {agree}.isSome',
            f'#eval IO.println ("AUTOFORM_L1CE {t} " ++ toString ((l1dom_{t}).findIdx? '
            f'(fun p => !(l1agree_{t} {args}))))',
            f'#eval IO.println ("AUTOFORM_L1CMP {t} " ++ toString (((l1dom_{t}).filter '
            f'(fun p => l1cmp_{t} {args})).length))',
            f'theorem l1bounded_{t} : (l1dom_{t}).all (fun p => l1agree_{t} {args}) = true := by\n'
            f'  decide +kernel',
            f'#print axioms l1bounded_{t}',
        ]) + '\n'

    def blueprint(self, model_tr: dict, deep_tr: dict, lean_root: Path, bounded: dict) -> str:
        lines = [
            'Prove that an AI-written Lean model of a function computes exactly what the deep '
            'translation of the same source function computes, for every argument of this shape.',
            f'LEFT side: `{self.lhs}` — the dispatcher `call` of the model module decodes the '
            f'arguments, runs the plain def `{self.model.get("lean_name", "")}` and encodes the result '
            '(an exception is `.exn (.str "<Class>")`). Unfold `call` and the def with `simp [...]`.',
            'Model source (Lean):\n' + (self.model.get('lean_source') or '')[:2500],
            f'RIGHT side: `{self.rhs}` — the Core interpreter `runFunc` running the Joern-derived '
            f'deep translation {deep_tr.get("program_const", "")}; `af_eval` head-normalizes `runFunc ...`.',
        ]
        if not deep_tr.get('call_template', '').startswith('runFunc'):
            lines.append('The right side starts from the initialized module heap (the function reads module '
                         'state): unfold its `call`/`callF`/`callH` (and `ctx`, `init`) with `simp only [...]` or '
                         '`unfold`, then evaluate; `decide +kernel` works for closed instances.')
        body = deep_body(lean_root, deep_tr, self.deep_fn['name'])
        if body:
            lines.append('Deep translation of the function (Lean, Core AST):\n' + body[:2500])
        if self.deep_fn.get('source'):
            lines.append(f"Original source ({self.deep_fn.get('file', '')}):\n" + self.deep_fn['source'][:2000])
        if bounded.get('status') == 'AGREES':
            lines.append(f"Evidence: the two sides agree on all {bounded.get('compared')} comparable points of "
                         f"a {bounded.get('points')}-point domain (kernel-checked bounded check).")
        lines.append('Typical proof: `intro ...`, `af_eval`, then `simp [<model>.call, <model def>]`, and for '
                     'branches `split`/`by_cases`/`omega`; Python `//` is `Int.fdiv`, `%` is `Int.fmod`.')
        return '\n'.join(lines)


def deep_body(lean_root: Path, deep_tr: dict, name: str) -> str:
    """The `def f_... : Func := { name := "<name>" ... }` block of the deep module, if found."""
    f = Path(lean_root) / 'Autoform/Generated' / f"{deep_tr.get('module', '')}.lean"
    try:
        text = f.read_text()
    except OSError:
        return ''
    i = text.find(f'{{ name := {lean_str(name)}')
    if i < 0:
        return ''
    start = text.rfind('\ndef ', 0, i)
    end = text.find('\n\n', i)
    return text[start + 1 if start >= 0 else i:end if end > 0 else i + 3000].strip()


def _marker(out: str, key: str, tag: str):
    m = re.search(rf'^AUTOFORM_{key} {re.escape(tag)} (.*)$', out, re.M)
    return m.group(1).strip() if m else None


def bounded_check(shapes: list, prefix: str, work: Path, lean_root: Path, stem: str) -> dict:
    """One Lean file for all shapes; {tag: {status, points, compared, disagreement, detail}}."""
    from ..harness.verifier import axioms_of, certified, run_lean
    work.mkdir(parents=True, exist_ok=True)
    f = work / f'{stem}_l1bounded.lean'
    f.write_text(prefix + L1EQ + '\n' + '\n'.join(s.bounded_block() for s in shapes))
    code, out, secs = run_lean(lean_root, f, LEAN_TIMEOUT)
    axioms = axioms_of(out)
    res = {}
    for s in shapes:
        r = {'points': len(s.points), 'file': str(f), 'seconds': secs}
        ce, cmp_ = _marker(out, 'L1CE', s.tag), _marker(out, 'L1CMP', s.tag)
        m = re.search(r'some (\d+)', ce or '')
        if code == 124:
            r.update(status='ERROR', detail=f'Lean exceeded {LEAN_TIMEOUT}s')
        elif m:
            point = s.points[int(m.group(1))]
            r.update(status='DISAGREES', disagreement=dict(zip(s.names, point)),
                     detail='model and deep translation give different results at this point '
                            '(compiled evaluation)')
        elif ce is None or cmp_ is None:
            r.update(status='ERROR', detail='bounded check produced no result: ' + out[-600:])
        elif certified(f'l1bounded_{s.tag}', axioms):
            r.update(status='AGREES', compared=int(cmp_),
                     detail=f'l1bounded_{s.tag} kernel-checked; {cmp_}/{len(s.points)} points comparable')
        else:
            r.update(status='ERROR', detail='no disagreement found but the bounded theorem was not accepted')
        res[s.tag] = r
    return res


def refine(translation: dict, models: list, deep_translation: dict, out_dir, *, statements=None,
           budget_usd: float | None = None, agent=None, lean_root=None, attempts: int = 2,
           cache_dir=DEFAULT_CACHE, domain_size: int = 64, parallel: int = 2, bounded: bool = True) -> list:
    """Attempt L1 for each validated model; write out_dir/refine.json; return [L1Result]."""
    from ..harness import prover
    model_tr, deep_tr = _d(translation), _d(deep_translation)
    out = Path(out_dir)
    work = out / 'refine'
    work.mkdir(parents=True, exist_ok=True)
    root = Path(lean_root or model_tr.get('lean_root') or deep_tr.get('lean_root')).resolve()
    model_fns = {f['name']: f for f in map(_d, model_tr.get('functions', []))}
    deep_fns = [_d(f) for f in deep_tr.get('functions', [])]
    by_fn: dict = {}
    for s in map(_d, statements or []):
        if s.get('elaborates'):
            by_fn.setdefault(s.get('function'), []).append(s)
    prefix = header(model_tr, deep_tr)

    results, plans, used = [], {}, set()
    for m in map(_d, models or []):
        fname = m.get('function')
        fn = model_fns.get(fname) or {'name': fname, 'source_name': fname, 'params': []}
        r = L1Result(fname, None, 'SKIPPED', m.get('level') or 'none')
        results.append(r)
        if m.get('status') != 'VALIDATED' or m.get('level') not in ('L0', 'L1'):
            r.reason = f"model is not validated (status {m.get('status')}, level {m.get('level')})"
            continue
        deep = pair(fn, deep_fns)
        if deep is None:
            r.reason = 'no deep translation of this function'
            continue
        r.deep_function = deep['name']
        if not deep.get('hole_free') or not deep.get('call_closed'):
            r.reason = ('deep translation has holes' if not deep.get('hole_free')
                        else 'deep translation calls untranslated functions')
            continue
        kinds = []
        sig = signature_shape(m.get('signature', ''))
        if sig is not None:
            kinds.append(sig)
        for s in by_fn.get(fname, []):
            k = statement_shape(s)
            if k is not None and k not in kinds:
                kinds.append(k)
        if not kinds:
            r.reason = f"no argument shape with a Val encoding (signature {m.get('signature')!r})"
            continue
        try:
            plans[fname] = [Shape(i, k, fn, deep, model_tr, deep_tr, m, domain_size, len(kinds) > 1, used)
                            for i, k in enumerate(kinds)]
        except (ValueError, KeyError) as exc:
            r.reason = f'cannot state L1: {exc}'
            plans.pop(fname, None)

    checks: dict = {}
    if bounded and plans:
        every = [s for ss in plans.values() for s in ss]
        try:
            checks = bounded_check(every, prefix, work, root, 'all')
        except Exception as exc:  # noqa: BLE001 - the filter is optional
            checks = {s.tag: {'status': 'ERROR', 'detail': f'bounded check failed: {exc!r}'} for s in every}

    jobs = []
    for r in results:
        for s in plans.get(r.function, []):
            b = checks.get(s.tag, {'status': 'NOT_RUN'})
            entry = {'kinds': list(s.kinds), 'theorem': s.theorem, 'statement': s.statement, 'bounded': b,
                     'status': 'PENDING'}
            r.shapes.append(entry)
            if b.get('status') == 'DISAGREES':
                entry.update(status='DISAGREES', reason=f"bounded check: {b.get('detail')} {b.get('disagreement')}")
                continue
            jobs.append((r, entry, prover.Job(name=s.theorem, prefix=prefix, statement=s.statement,
                                              blueprint=s.blueprint(model_tr, deep_tr, root, b))))
    if jobs:
        done = prover.prove_many([j for _, _, j in jobs], root, work / 'prover', parallel=parallel,
                                 budget_usd=budget_usd, agent=agent, attempts=attempts, cache_dir=cache_dir)
        for (r, entry, _), res in zip(jobs, done):
            why = '' if res.status == 'PROVED' else (
                ('budget exhausted: ' if res.status == 'BUDGET' else
                 'agent timed out: ' if res.status == 'TIMEOUT' else '') + (res.reason or res.status)[:2000])
            entry.update(status='PROVED' if res.status == 'PROVED' else 'FAILED', proof=res.proof,
                         certificate=res.certificate, axioms=res.axioms, cost_usd=res.cost_usd,
                         cached=res.cached, reason=why)
            r.cost_usd += res.cost_usd
    for r in results:
        if not r.shapes:
            continue
        st = [e['status'] for e in r.shapes]
        if all(x == 'PROVED' for x in st):
            r.status, r.level = 'PROVED', 'L1'
            r.reason = ('model proved equal to the deep translation for every argument shape; proofs about the '
                        'model at these shapes transfer to the deep translation')
        else:
            r.status = 'DISAGREES' if 'DISAGREES' in st else 'FAILED'
            r.level = 'L0'
            bad = next(e for e in r.shapes if e['status'] != 'PROVED')
            r.reason = f"{bad['theorem']} ({','.join(bad['kinds']) or 'no args'}): {bad.get('reason') or bad['status']}"
        r.cost_usd = round(r.cost_usd, 4)
    dump(results, out / FILES['refine'])
    return results
