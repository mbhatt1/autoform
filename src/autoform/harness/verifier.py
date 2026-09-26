"""Verification engine: Lean kernel backend, structural backend, native witness replay.

Result taxonomy (never PASS/FAIL):
  PROVED                universal statement closed by a Lean proof (standard axioms only)
  BOUNDED_PROVED        kernel-checked by computation over the stated finite domain
  REFUTED               kernel-checked witness: the claim is false under the model
  UNKNOWN               neither proved nor refuted
  TIMEOUT               the backend exceeded its deadline
  UNSUPPORTED           no available backend can express the claim
  MODEL_INCOMPLETE      evaluation reaches an unmodeled construct (hole/outOfFuel) or
                        the function reaches an UNSUPPORTED external
  ASSUMPTION_DEPENDENT  proved, but only under claim-level assumptions stated in prose
  INCONSISTENT_MODEL    compiled evaluation and kernel evaluation disagree

Soundness contract: Proof(c) ⇒ Semantics_M(P) ⊨ c for the Core interpreter M, never
RealWorld(P) ⊨ c. Native replay is evidence about M's fidelity, not part of the proof.
"""
from __future__ import annotations

import json
import os
import re
import signal
import subprocess
import time
from pathlib import Path

from . import claims as C
from .compiler import DEEP_TACTIC, UNIVERSAL_TACTIC, Obligation, header
from .cpir import sha256

STATUSES = ('PROVED', 'BOUNDED_PROVED', 'REFUTED', 'UNKNOWN', 'TIMEOUT', 'UNSUPPORTED',
            'MODEL_INCOMPLETE', 'ASSUMPTION_DEPENDENT', 'INCONSISTENT_MODEL')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
LEAN_OPS = C.COMPARE | C.BOOLEAN | set(C.ARITH) | C.OUTCOME

# Capability matrix (design §21). `available` is decided at run time, never assumed.
BACKENDS = {
    'lean-kernel': dict(text='Lean 4 kernel over the Core interpreter: universal proof attempt, '
                             'kernel-checked finite-domain proof, kernel-checked witnesses.',
                        expresses=LEAN_OPS, bitvectors=True, recursion='by computation',
                        loops='by computation', concurrency=False, certificate='Lean proof term'),
    'cpir-structural': dict(text='Deterministic structural check over the CPIR call/write order '
                                 '(every path, structured control flow).',
                            expresses=C.STRUCTURAL, concurrency=False, certificate='replayable graph query'),
    'z3': dict(text='SMT (bitvectors, integers); needs an SMT encoding of the function body.',
               expresses=C.COMPARE | C.BOOLEAN | set(C.ARITH), available=False,
               reason='no SMT lowering of Core functions is implemented; results would not be certified'),
    'chc': dict(text='Constrained Horn clauses (loops, invariants).', expresses=set(), available=False,
                reason='not integrated'),
    'cbmc': dict(text='Bounded model checking for C memory safety.', expresses=set(), available=False,
                 reason='not integrated'),
    'angr': dict(text='Binary symbolic execution.', expresses=set(), available=False,
                 reason='not integrated; see autoform machine for the p-code path'),
    'model-checker': dict(text='Temporal properties over state machines.', expresses=set(), available=False,
                          reason='not integrated'),
}


def feasible_backends(claim) -> list:
    ops = C.operators(claim['property']) | {o for p in claim['preconditions'] for o in C.operators(p)}
    out = []
    for name, b in BACKENDS.items():
        if b.get('available', True) is False:
            continue
        if ops and ops <= b['expresses']:
            out.append(dict(id=name, text=b['text']))
    return out


# --- Lean runner ---------------------------------------------------------------

def run_lean(root: Path, path: Path, timeout: int):
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ.get('PATH', ''))
    started = time.time()
    proc = subprocess.Popen(['lake', 'env', 'lean', str(path)], cwd=root, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, start_new_session=True)
    try:
        out, _ = proc.communicate(timeout=timeout)
        code = proc.returncode
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        out, _ = proc.communicate()
        code = 124
    return code, out or '', round(time.time() - started, 2)


def axioms_of(output: str) -> dict:
    found = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        found[m.group(1)] = {a.strip() for a in m.group(2).split(',') if a.strip()}
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", output):
        found[m.group(1)] = set()
    return found


def certified(name, axioms) -> bool:
    return name in axioms and axioms[name] <= ALLOWED_AXIOMS


def build_status(root: Path, module: str, build: bool = False, timeout: int = 3600) -> dict:
    """Refuse to verify against a model whose build is out of date.

    `lake build --no-build` is lake's own freshness check (exit 0 = up to date). A stale
    olean can silently encode an older interpreter, so it is never used. With `build`,
    only this module and its out-of-date dependencies are rebuilt.
    """
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ.get('PATH', ''))
    target = f'Autoform.Generated.{module}'
    src = Path(root) / 'Autoform/Generated' / f'{module}.lean'
    if not src.is_file():
        return dict(ok=False, reason=f'{src} does not exist; translate the source first (autoform source)')
    command = ['lake', 'build', target] + ([] if build else ['--no-build'])
    try:
        proc = subprocess.run(command, cwd=root, env=env, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return dict(ok=False, reason=f'{" ".join(command)} exceeded {timeout}s')
    if proc.returncode != 0:
        return dict(ok=False, reason=(f'{target} is not built or is out of date; rerun with --build '
                                      f'or run: lake build {target}') if not build else
                    f'lake build {target} failed: {proc.stdout[-800:]}')
    return dict(ok=True, model_sha256=sha256(src.read_bytes()))


class LeanBackend:
    name = 'lean-kernel'

    def __init__(self, root: Path, module: str, workdir: Path, timeout=300, fuel=1000, universal=True,
                 deep=False):
        self.root, self.module, self.workdir = Path(root), module, Path(workdir)
        self.timeout, self.fuel, self.universal = timeout, fuel, universal
        self.tactic = DEEP_TACTIC if deep else UNIVERSAL_TACTIC
        self.workdir.mkdir(parents=True, exist_ok=True)
        toolchain = Path(root) / 'lean-toolchain'
        self.version = toolchain.read_text().strip() if toolchain.is_file() else 'unknown'

    CHUNK = 24

    def verify(self, claims_fns, program) -> dict:
        """Verify claims in chunks; each chunk is two Lean runs (search, then certify).
        Chunks run one at a time: each Lean process holds the whole model in memory."""
        results = {}
        for i in range(0, len(claims_fns), self.CHUNK):
            results.update(self._verify_chunk(claims_fns[i:i + self.CHUNK], program, i // self.CHUNK))
        return results

    def _verify_chunk(self, claims_fns, program, index) -> dict:
        obls = {c['id']: Obligation(c, fn, program, self.module, self.fuel) for c, fn in claims_fns}
        results = {cid: dict(backend=self.name, backend_version=self.version) for cid in obls}
        if not obls:
            return results
        # Run 1: definitions, universal attempts, bounded proofs, witness search.
        text = [header(self.module)]
        for cid, ob in obls.items():
            text += [ob.check_def(), ob.domain_def()]
            if self.universal:
                text.append(f'theorem univ_{ob.tag} : {ob.prop()} := by\n  {self.tactic}\n')
            text.append(f'theorem bounded_{ob.tag} : (dom_{ob.tag}).all (fun p => {ob.apply()}) = true := by\n'
                        f'  decide +kernel\n')
            text.append(ob.search())
            if self.universal:
                text.append(f'#print axioms univ_{ob.tag}\n')
            text.append(f'#print axioms bounded_{ob.tag}\n')
        first = self.workdir / f'{self.module}_obligations_{index}.lean'
        first.write_text('\n'.join(text))
        code, out, secs = run_lean(self.root, first, self.timeout)
        axioms = axioms_of(out)
        witnesses = {m.group(1): json.loads(m.group(2)) for m in re.finditer(r'AUTOFORM_CE (\S+) (\[.*\])', out)}
        nowit = set(re.findall(r'AUTOFORM_NOCE (\S+)', out))
        for cid, ob in obls.items():
            r = results[cid]
            r.update(lean_file=str(first), lean_file_sha256=sha256(first.read_bytes()), seconds=secs,
                     domain_size=len(ob.points), domain_points_in_precondition=ob.points_in_pre(),
                     statement=ob.prop())
            if code == 124:
                r.update(status='TIMEOUT', reason=f'Lean exceeded {self.timeout}s')
                continue
            if code not in (0, 1):
                r.update(status='UNKNOWN', reason=f'Lean exited with {code}; see {first.name}',
                         log_tail=out[-2000:])
                continue
            univ = certified(f'univ_{ob.tag}', axioms)
            bounded = certified(f'bounded_{ob.tag}', axioms)
            r.update(universal_proof=univ, bounded_proof=bounded,
                     theorems=[t for t, ok in ((f'univ_{ob.tag}', univ), (f'bounded_{ob.tag}', bounded)) if ok])
            if cid in witnesses:
                r['witness_candidate'] = witnesses[cid]
                if bounded:
                    r.update(status='INCONSISTENT_MODEL',
                             reason='compiled evaluation reports a failing point but the kernel proved the '
                                    'domain; the evaluator and the kernel disagree')
            elif cid not in nowit:
                r.update(status='UNKNOWN', reason='witness search produced no result', log_tail=out[-2000:])
        # Run 2: certify witnesses in the kernel and record the model's outcome at them.
        pending = {cid: ob for cid, ob in obls.items() if 'witness_candidate' in results[cid]
                   and 'status' not in results[cid]}
        if pending:
            text = [header(self.module)]
            for cid, ob in pending.items():
                point = results[cid]['witness_candidate']
                text += [ob.check_def(),
                         f'theorem refute_{ob.tag} : {ob.apply_point(point)} = false := by\n  decide +kernel\n',
                         f'#print axioms refute_{ob.tag}\n',
                         f'#eval IO.println ("AUTOFORM_OUTCOME {cid} " ++ (Lean.toJson (toString (repr ({ob.outcome_call(point)}))))'
                         f'.compress)\n']
            second = self.workdir / f'{self.module}_witnesses_{index}.lean'
            second.write_text('\n'.join(text))
            code2, out2, secs2 = run_lean(self.root, second, self.timeout)
            ax2 = axioms_of(out2)
            outcomes = {m.group(1): json.loads(m.group(2)) for m in re.finditer(r'AUTOFORM_OUTCOME (\S+) (".*")', out2)}
            for cid, ob in pending.items():
                r = results[cid]
                r.update(witness_file=str(second), witness_file_sha256=sha256(second.read_bytes()))
                outcome = outcomes.get(cid, '')
                r['witness'] = dict(inputs={fn_param: v for fn_param, v in
                                            zip([ob.fn.param(b['param']).name for b in ob.claim['forall']],
                                                r['witness_candidate'])},
                                    model_outcome=outcome, outcome_kind=outcome_kind(outcome))
                if code2 == 124:
                    r.update(status='TIMEOUT', reason='witness certification exceeded its deadline')
                elif certified(f'refute_{ob.tag}', ax2):
                    r['theorems'] = r.get('theorems', []) + [f'refute_{ob.tag}']
                    r['status'] = 'REFUTED'
                else:
                    r.update(status='INCONSISTENT_MODEL',
                             reason='compiled evaluation found a failing point the kernel does not confirm')
        for cid, ob in obls.items():
            r = results[cid]
            if 'status' in r:
                continue
            if r.get('universal_proof'):
                r['status'] = 'PROVED'
            elif r.get('bounded_proof'):
                if r['domain_points_in_precondition'] == 0:
                    r.update(status='UNKNOWN', reason='bounded proof is vacuous: no domain point meets the '
                                                      'preconditions')
                else:
                    r['status'] = 'BOUNDED_PROVED'
            else:
                r.update(status='UNKNOWN', reason='no proof and no witness; see ' + first.name)
        return results


def outcome_kind(repr_text: str) -> str:
    if 'EResult.hole' in repr_text and '"ub:' in repr_text:
        return 'undefined_behavior'
    for kind, key in (('value', 'EResult.val'), ('exception', 'EResult.exn'), ('hole', 'EResult.hole'),
                      ('out_of_fuel', 'EResult.outOfFuel')):
        if key in repr_text:
            return kind
    return 'unknown'


def parse_value(repr_text: str):
    """Best-effort decode of a Core value repr for native comparison (int/bool/str only)."""
    m = re.search(r'Val\.int (\(?-?\d+\)?)', repr_text)
    if m and 'EResult.val' in repr_text:
        return ('value', int(m.group(1).strip('()')))
    m = re.search(r'Val\.bool (true|false)', repr_text)
    if m and 'EResult.val' in repr_text:
        return ('value', m.group(1) == 'true')
    m = re.search(r'Val\.str (".*?")', repr_text)
    if m and 'EResult.val' in repr_text:
        return ('value', json.loads(m.group(1)))
    if 'EResult.exn' in repr_text:
        return ('exception', None)
    return None


# --- structural backend ------------------------------------------------------------

class StructuralBackend:
    """Must-precede analysis over the structured Core AST (no gotos; every path)."""
    name = 'cpir-structural'

    def __init__(self, ast: dict):
        self.ast = ast  # function name -> body

    def verify(self, claim, fn) -> dict:
        body = self.ast.get(fn.name)
        holes = bool(fn.holes)
        prop = claim['property']
        ok, witness = self._eval(prop, body)
        r = dict(backend=self.name, backend_version='1', certificate='structural re-check of the Core AST')
        if ok:
            r['status'] = 'MODEL_INCOMPLETE' if holes else 'PROVED'
            if holes:
                r['reason'] = 'the function contains untranslated statements the check cannot see'
        else:
            r.update(status='REFUTED', witness=dict(path=witness))
        return r

    def _eval(self, f, body):
        op = f['op']
        if op == 'AND':
            for a in f['args']:
                ok, w = self._eval(a, body)
                if not ok:
                    return ok, w
            return True, None
        if op == 'OR':
            ws = []
            for a in f['args']:
                ok, w = self._eval(a, body)
                if ok:
                    return True, None
                ws.append(w)
            return False, ws
        if op == 'NOT':
            ok, _ = self._eval(f['args'][0], body)
            return (not ok), (None if not ok else 'negated structural fact holds')
        calls = _calls_in_order(body)
        if op == 'CALLS':
            return (f['callee'] in calls), (None if f['callee'] in calls else f'{f["callee"]} is never called')
        if op == 'NOT_CALLS':
            return (f['callee'] not in calls), (None if f['callee'] not in calls else f'{f["callee"]} is called')
        if op in ('WRITES', 'NO_WRITE'):
            writes = _writes(body)
            hit = f['target'] in writes
            return (hit if op == 'WRITES' else not hit), None if (hit == (op == 'WRITES')) else f'write set {writes}'
        if op == 'BEFORE':
            return _must_precede(body, f['first'], f['then'])
        raise ValueError(op)


def _callee(node):
    k = node.get('k')
    if k == 'call':
        return node.get('f')
    if k == 'mcall':
        return '.' + str(node.get('m'))
    return None


def _calls_in_order(node) -> list:
    out, stack = [], [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, dict):
            c = _callee(cur)
            if c:
                out.append(c)
            stack.extend(reversed([v for k, v in cur.items() if k != 'k']))
        elif isinstance(cur, list):
            stack.extend(reversed(cur))
    return out


def _writes(node) -> set:
    out, stack = set(), [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, dict):
            if cur.get('k') in ('setGlobal', 'del'):
                out.add(str(cur.get('x')))
            elif cur.get('k') in ('setField',):
                out.add(str(cur.get('f')))
            stack.extend(v for k, v in cur.items() if k != 'k')
        elif isinstance(cur, list):
            stack.extend(cur)
    return out


def _must_precede(body, first, then):
    """Every evaluation of a `then` call is preceded, on its path, by a completed `first` call.

    Abstract state: `done` = `first` has certainly been called on every path reaching here.
    Branches meet with AND; loops are analyzed with `done` as it is at loop entry (a call
    inside an earlier iteration is not assumed); raise/return end a path.
    """
    violation = []

    def expr(node, done):
        # evaluation order: arguments before the call itself
        if isinstance(node, list):
            for v in node:
                done = expr(v, done)
            return done
        if not isinstance(node, dict):
            return done
        k = node.get('k')
        if k == 'cond':
            done = expr(node.get('c'), done)
            return expr(node.get('t'), done) and expr(node.get('e'), done)
        for key, v in node.items():
            if key != 'k':
                done = expr(v, done)
        c = _callee(node)
        if c == then and not done:
            violation.append(f'{then} reachable without a preceding {first}')
        if c == first:
            done = True
        return done

    def stmt(node, done):
        if not isinstance(node, dict):
            return done
        k = node.get('k')
        if k == 'seq':
            return stmt(node.get('b'), stmt(node.get('a'), done))
        if k == 'ifte':
            done = expr(node.get('c'), done)
            return stmt(node.get('t'), done) and stmt(node.get('e'), done)
        if k in ('loop', 'forIn'):
            entry = expr(node.get('c') if k == 'loop' else node.get('e'), done)
            stmt(node.get('body'), entry)
            return entry
        if k == 'tryCatch':
            after = stmt(node.get('body'), done)
            stmt(node.get('handler'), done)
            return after and done
        if k == 'tryFinally':
            return stmt(node.get('fin'), stmt(node.get('body'), done))
        if k == 'breakBlock':
            stmt(node.get('body'), done)
            return done
        return expr({key: v for key, v in node.items() if key != 'k'}, done)

    stmt(body, False)
    return (not violation), (violation[0] if violation else None)


# --- native witness replay (design §32) --------------------------------------------

NATIVE_RUNNER = r'''
import importlib.util, json, sys
path, name, args = sys.argv[1], sys.argv[2], json.loads(sys.argv[3])
spec = importlib.util.spec_from_file_location("autoform_subject", path)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
try:
    value = getattr(mod, name)(*args)
    print(json.dumps({"kind": "value", "value": value if isinstance(value, (int, bool, str)) else repr(value),
                      "type": type(value).__name__}))
except Exception as exc:
    print(json.dumps({"kind": "exception", "type": type(exc).__name__}))
'''


def native_replay(source: Path | None, fn, inputs: list, timeout=10) -> dict:
    """Run the real Python function on the witness; compare with the model's outcome."""
    if not source or not fn.file.endswith('.py') or not fn.source_name or '.' in fn.name.split('<module>.', 1)[-1]:
        return dict(status='not_run', reason='native replay supports top-level Python functions only')
    path = Path(source) / fn.file
    if not path.is_file():
        return dict(status='not_run', reason='source file unavailable')
    try:
        proc = subprocess.run(['python3', '-c', NATIVE_RUNNER, str(path), fn.source_name, json.dumps(inputs)],
                              cwd=path.parent, capture_output=True, text=True, timeout=timeout)
        line = proc.stdout.strip().splitlines()[-1] if proc.stdout.strip() else ''
        return dict(status='ran', result=json.loads(line)) if line else \
            dict(status='error', reason=proc.stderr[-500:])
    except (subprocess.TimeoutExpired, json.JSONDecodeError) as exc:
        return dict(status='error', reason=str(exc))


def native_agrees(native: dict, model_repr: str):
    if native.get('status') != 'ran':
        return None
    decoded = parse_value(model_repr)
    if decoded is None:
        return None
    res = native['result']
    if decoded[0] == 'exception':
        return res['kind'] == 'exception'
    return res['kind'] == 'value' and res.get('value') == decoded[1] and \
        type(res.get('value')) is type(decoded[1])
