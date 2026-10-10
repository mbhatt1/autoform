"""Formalize stage: English properties -> Lean statements about the translated function.

For each `EnglishProperty` the model proposes only the *pieces* of a statement:

    binders  one per function parameter, in order: a Lean name and a type (Int/Bool/String,
             or Val for an object, container or other value, passed as is)
    observe  (methods only) "post" to state a property of the receiver after the call: the
             call is then `<name>#post`, whose value is `.tuple [result, receiver']`
    pre      a Lean `Bool` over the binders
    post     a Lean `Bool` over the binders and `r : EResult`

and this module assembles the proposition itself, always in the canonical shape

    ∀ (a : Int) (b : Int), ((pre : Bool)) = true → (fun (r : EResult) => (post : Bool)) (<call>) = true

(the `: Bool` ascriptions only fix the elaboration type; a decidable Prop is coerced by
`decide`, so the statement is still definitionally the plain canonical shape)

with `<call>` built from `translation['call_template']`. Because the shape is assembled here
rather than written by the model, `lean_prop` is *syntactically* the canonical form, so the
check stage can evaluate `pre`/`post` on concrete inputs and be sure it is testing the same
statement. The model cannot leave out the call or smuggle in a different one.

Elaboration loop. Each candidate is written to a scratch file under `out_dir/scratch/`:

    import Autoform.Generated.<M>
    #check fun (a : Int) (b : Int) => ((pre) : Bool)
    #check fun (a : Int) (b : Int) (r : EResult) => ((post) : Bool)
    theorem <id> : <lean_prop> := by sorry

and checked with `lake env lean` from `translation['lean_root']`. Any error (or a shape
problem found before Lean runs) is fed back to the model with the numbered scratch file, for
up to `repairs` rounds. We drive the loop from Python instead of handing the model a
`./check.sh` tool: the number of concurrent Lean processes stays bounded by this module
(`LEAN_SLOTS`), every model call is a plain text call that `llm.ask` caches on disk (tool
calls are never cached), a round costs one short completion rather than a multi-turn agent
session, and the verdict "elaborates" is decided by our own Lean run, never reported by
the model.

Nothing here decides truth: an elaborating statement may be false. That is the check and
prove stages' job.
"""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from . import llm, pyvalues as pv, schema

LEAN_SLOTS = threading.BoundedSemaphore(3)   # max concurrent Lean processes, process-wide
LEAN_TIMEOUT = 600

TYPES = {'Int': '.int', 'Bool': '.bool', 'String': '.str', 'Val': ''}
SORT_TYPES = {'int': {'Int'}, 'bool': {'Bool'}, 'str': {'String'}, 'object': {'Val'}}   # 'any'/'float': free
RECEIVER_KINDS = ('method', 'property')
KEYWORDS = {
    'at', 'by', 'do', 'else', 'end', 'from', 'fun', 'have', 'if', 'import', 'in', 'let',
    'match', 'namespace', 'open', 'section', 'show', 'then', 'theorem', 'with', 'where',
    'def', 'deriving', 'instance', 'structure', 'class', 'variable', 'universe', 'return',
    'for', 'mut', 'unless', 'try', 'catch', 'finally', 'true', 'false', 'r', 'Type', 'Prop',
    'Sort', 'this', 'calc', 'suffices', 'obtain', 'nomatch', 'nofun', 'termination_by',
}
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
MENTIONS_R = re.compile(r"(?<![\w.'`])r(?![\w'])")


# ---------------------------------------------------------------- small Lean helpers

def lean_string(s: str) -> str:
    """A Lean string literal for `s`."""
    out = s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n').replace('\t', '\\t')
    return '"' + out + '"'


def sanitize(name: str) -> str:
    s = re.sub(r'[^A-Za-z0-9_]+', '_', name).strip('_')
    s = re.sub(r'_+', '_', s)
    if not s or not s[0].isalpha():
        s = 'f_' + s
    return s


def statement_id(function: str, prop_id: str) -> str:
    return f'{sanitize(function)}__{sanitize(prop_id)}'


def build_call(template: str, name: str, args: list) -> str:
    return (template.replace('{name}', lean_string(name))
            .replace('{args}', '[' + ', '.join(args) + ']'))


def receiver_guard(fn: dict, binders: list, namespace: str) -> str:
    """`(dObj_S self).isSome` for a method or property: the statement is about real receivers.

    Without it `self` ranges over every Val (`.unit`, objects of other classes), the dispatcher
    returns a hole there, and the statement is false for a reason that says nothing about the code."""
    types = fn.get('lean_types') or []
    if not namespace or fn.get('kind') not in RECEIVER_KINDS or not binders or not types or not IDENT.match(str(types[0])) \
            or types[0] in TYPES or binders[0].get('type') != 'Val':
        return ''
    return f"({namespace}.dObj_{types[0]} {binders[0]['name']}).isSome"


def with_receiver_guard(fn: dict, cand: dict, translation: dict) -> dict:
    guard = receiver_guard(fn, cand['binders'], schema.model_namespace(translation))
    if not guard or guard in cand['pre']:
        return cand
    pre = cand['pre'].strip()
    return dict(cand, pre=guard if pre in ('', 'true') else f'{guard} && ({pre})')


def binder_val(b: dict) -> str:
    return f"{TYPES[b['type']]} {b['name']}".strip()


def assemble(binders: list, pre: str, post: str, call: str) -> str:
    """The canonical proposition; the check stage relies on exactly this shape."""
    head = ''.join(f"∀ ({b['name']} : {b['type']}), " for b in binders)
    return f'{head}((({pre}) : Bool)) = true → (fun (r : EResult) => (({post}) : Bool)) ({call}) = true'


# ---------------------------------------------------------------- prompt

VOCABULARY = r'''
## The Lean vocabulary (namespace `Autoform.Core`, already opened)

A translated function is run with `runFunc program fuel name args : EResult`, where the
arguments are a `List Val`. You never write that call yourself: the harness builds it from
your binders. You only write two Lean `Bool` expressions, `pre` and `post`.

inductive Val where
  | int   : Int → Val            -- Python int, every C/Java/Go integer (after the cast)
  | str   : String → Val
  | bool  : Bool → Val           -- Python bool (True/False)
  | float : Fl → Val             -- IEEE float (bits), see below
  | unit  : Val                  -- Python None / C void
  | list  : List Val → Val
  | tuple : List Val → Val
  | dict  : List (Val × Val) → Val
  | ref   : Nat → Val            -- heap object
  ... (fn, clos, bobj: rarely needed)

inductive EResult where
  | val       : Val → EResult    -- normal return value
  | exn       : Val → EResult    -- raised exception; builtins are `.exn (.str "ZeroDivisionError")`,
                                 --   `.exn (.str "TypeError")`, `.exn (.str "ValueError")`, ...
  | hole      : String → EResult -- an untranslated construct was reached
  | outOfFuel : EResult

Facts about the model:
* A Python function returning True/False returns `.val (.bool b)`; returning an int gives
  `.val (.int n)`; returning a str gives `.val (.str s)`; returning None gives `.val .unit`.
* C/Java/Go functions return `.val (.int n)` with the value already cast to the declared
  width (unsigned wraps to [0, 2^w), signed wraps to [-2^(w-1), 2^(w-1))). A C "boolean"
  (comparison result) is `.val (.int 0)` or `.val (.int 1)`.
* Python `bool` is not an `int` in this model (`True + 1` hits a hole): use `Int` binders for
  integer properties.
* `Val.beq : Val → Val → Bool` (also `==` on `Val`) is Python-style value equality
  (`.int 1 == .float 1.0`, floats by value, lists/tuples/dicts structurally).
* Int arithmetic in Lean: `a + b`, `a - b`, `a * b`, `a ^ n` (n : Nat), `Int.fdiv a b` (floor
  division = Python `//`), `Int.fmod a b` (Python `%`), `Int.tdiv`/`Int.tmod` (C `/`, `%`),
  `a % m` (Euclidean, nonnegative for m > 0: unsigned wrap is `(a + b) % 2^32`),
  `Int.bmod x (2^32)` (signed 32-bit wrap), `Int.natAbs`. Lean's plain `a / b` on Int is
  Euclidean division — do NOT use it for Python `//` or C `/`.
* Comparisons: `a == b`, `a != b` are Bool. `a < b`, `a ≤ b` are Props; inside a Bool write
  `decide (a < b)` (or rely on the automatic coercion). Connectives: `&&`, `||`, `!`.
  Strings: `s ++ t`, `s.length`, `s == t`.
* Floats: `.float x` with `x : Fl`. Useful: `Fl.isNaN x`, `Fl.isInf x`,
  `Fl.cmpIntv n x : Option Ordering` (exact compare of an Int with a float),
  `FConfig.python.ofInt n : FResult` and `FConfig.python.div x y : FResult`
  (`FResult.ok x` on success). E.g. "returns the correctly rounded a / b":
    match r with
    | .val (.float x) =>
      (match FConfig.python.ofInt a, FConfig.python.ofInt b with
       | .ok xa, .ok xb => (match FConfig.python.div xa xb with
                           | .ok q => Val.beq (.float x) (.float q) | _ => false)
       | _, _ => false)
    | _ => false
* Pattern tests: `r matches .exn (.str "ZeroDivisionError")`, or a full
  `match r with | .val (.int n) => ... | _ => false`. Always make the catch-all case `false`
  unless the English really allows any outcome: a hole or running out of fuel is not a
  normal return.
* Python data in `Val` (AI-model translations): a tuple is `.tuple vs`, a list `.list vs`, a
  dict `.dict kvs` (association list in insertion order), bytes `.bobj "bytes" (.list [.int b, ...])`,
  a set `.bobj "set" (.list elems)` (elements in a canonical sorted order, no duplicates), an
  object of a modelled class `.bobj "obj:<module>.<Class>" (.dict [(.str "<attr>", v), ...])`
  (instance attributes, sorted by name; private ones mangled as CPython does, e.g.
  `_Cache__data`). Helpers (total, usable in pre/post): `vField o "attr" : Val` (an object's
  attribute, `.unit` if absent), `vGet d k : Option Val` (dict lookup by Python equality),
  `vHas d k : Bool` (`k in d` for a dict, list, tuple or set), `vLen v : Int` (`len`),
  `vKeys d : List Val` (a dict's keys in order), `vElems v : List Val` (list/tuple/set elements).
* Binders of type `Val` range over values recorded from the project's tests (receivers,
  containers, ...), so use `Val` for a parameter whose Lean model type is not Int/Bool/String,
  and for the receiver `self` of a method (always `Val`). Constrain their shape in `pre`
  (e.g. `vHas (vField self "_Cache__data") k`). The harness adds `(<model namespace>.dObj_<Struct> self).isSome`
  to `pre` itself, so `self` is always a real object of the class; state any further
  invariant the property needs (e.g. that a size field matches the stored data).
* Methods. The first parameter of a method is its receiver `self` (an encoded object). By
  default `r` is the method's Python result. To state what the method does to the receiver,
  set "observe": "post": then `r` is `.val (.tuple [result, self'])` where `self'` is the
  receiver after the call, e.g. `match r with | .val (.tuple [_, s']) => vHas (vField s' "d") k
  | _ => false`; an exception is still `.exn (.str "E")`. A constructor (`__init__`) takes the
  arguments after `self` and returns the new object: `.val (.bobj "obj:..." (.dict ...))`.
'''

EXAMPLES = r'''
## Worked examples

1. Python `def add(a, b): return a + b`, English: "For all integers a and b, add(a, b)
   returns a + b."
   {"binders": [{"name": "a", "type": "Int"}, {"name": "b", "type": "Int"}],
    "pre": "true",
    "post": "match r with | .val (.int n) => n == a + b | _ => false"}

2. Python `def quotient(a, b): return a // b`, English: "If b is 0, quotient(a, b) raises
   ZeroDivisionError."
   {"binders": [{"name": "a", "type": "Int"}, {"name": "b", "type": "Int"}],
    "pre": "b == 0",
    "post": "r matches .exn (.str \"ZeroDivisionError\")"}
   and "otherwise it returns the floor of a / b":
   {"binders": [...same...], "pre": "b != 0",
    "post": "match r with | .val (.int n) => n == Int.fdiv a b | _ => false"}

3. Python `def authorize(owner, caller): return owner == caller`, English:
   "authorize(owner, caller) returns True exactly when owner equals caller."
   {"binders": [{"name": "owner", "type": "String"}, {"name": "caller", "type": "String"}],
    "pre": "true",
    "post": "match r with | .val (.bool t) => t == (owner == caller) | _ => false"}

4. C `uint32_t wrap(uint32_t a, uint32_t b) { return a + b; }`, English: "For unsigned 32-bit
   a and b, wrap(a, b) returns (a + b) modulo 2^32."
   {"binders": [{"name": "a", "type": "Int"}, {"name": "b", "type": "Int"}],
    "pre": "decide (0 ≤ a) && decide (a < 2^32) && decide (0 ≤ b) && decide (b < 2^32)",
    "post": "match r with | .val (.int n) => n == (a + b) % 2^32 | _ => false"}
   A C function with no parameters has "binders": [] and usually "pre": "true".
'''

RULES = r'''
## Rules
* Exactly one binder per function parameter, in parameter order; the i-th binder is passed
  as the i-th argument (`.int x` for Int, `.bool x` for Bool, `.str x` for String, `x` itself
  for Val). Reuse the
  parameter name unless it clashes with a Lean keyword; never name a binder `r`.
* To fix an argument to a constant ("quotient(a, 0)"), keep the binder and constrain it in
  `pre` (`b == 0`).
* Put input-domain assumptions (ranges, nonzero divisors) in `pre`; put the claim about the
  result in `post`. `pre` must not mention `r`; `post` must inspect `r`.
* Say exactly what the English says, no stronger and no weaker. Do not tailor the statement
  to what the code does if the English says something different: a false statement is a
  useful finding, a rewritten one is not.
* `pre` and `post` are single Lean expressions (newlines allowed); no `sorry`, no tactics,
  no `theorem`, no new definitions.
'''


def lean_body(translation: dict, fn: dict) -> str:
    """The function's `def` from the generated module, if it can be found."""
    models = [m for m in schema.lean_imports(translation) if m.startswith('Autoform.NLModel.')]
    if models:   # an AI model module: the section autoform.nl.model wrote for this function
        path = Path(translation['lean_root']).joinpath(*models[0].split('.')).with_suffix('.lean')
        try:
            text = path.read_text()
        except OSError:
            return ''
        m = re.search(r'^-- model of ' + re.escape(fn['name']) + r':.*?\n(.*?)^-- end model of ',
                      text, re.M | re.S)
        body = m.group(1).strip() if m else ''
        return body if len(body) <= 6000 else body[:6000] + '\n  ... (truncated)'
    path = Path(translation['lean_root']) / 'Autoform' / 'Generated' / (translation['module'] + '.lean')
    try:
        text = path.read_text()
    except OSError:
        return ''
    marker = f'{{ name := {lean_string(fn["name"])}'
    at = text.find(marker)
    if at < 0:
        return ''
    start = text.rfind('\ndef ', 0, at)
    end = text.find('\n\n', at)
    body = text[start + 1 if start >= 0 else at:end if end >= 0 else len(text)]
    return body if len(body) <= 6000 else body[:6000] + '\n  ... (truncated)'


def describe_function(translation: dict, fn: dict) -> str:
    params = ', '.join(p['name'] + (f": {p['sort']}" if p.get('sort') not in (None, '', 'any') else '')
                       + (f" ({p['integer_type']})" if p.get('integer_type') else '')
                       for p in fn['params'])
    lines = [f"Language: {translation.get('language', '?')}",
             f"Function: {fn.get('source_name') or fn['name']}({params})  -> {fn.get('returns', 'any')}",
             f"Qualified name in the Lean program: {fn['name']}",
             f"File: {fn.get('file', '?')}:{fn.get('line') or '?'}"]
    kind = fn.get('kind') or 'function'
    if fn.get('lean_types'):
        lines.append('Lean model parameter types: ' + ', '.join(
            f"{p['name']} : {t.lstrip('*')}" + (' (*varargs: not checkable on samples)' if t.startswith('*') else '')
            for p, t in zip(fn['params'], fn['lean_types'])))
    if kind in RECEIVER_KINDS:
        lines.append(f"This is a {'method' if kind == 'method' else 'property getter'} of {fn.get('receiver')}; "
                     f"the first parameter is the receiver (binder type Val). It "
                     + ('CAN CHANGE the receiver: "observe": "post" exposes the receiver after the call.'
                        if fn.get('mutates') else 'does not change the receiver.'))
    elif kind == 'constructor':
        lines.append(f"This is the constructor of {fn.get('receiver')}: it returns the new object.")
    if fn.get('samples'):
        lines.append('Example inputs recorded from the tests (Python view): ' + '; '.join(
            pv.show_args(p) for p in fn['samples'][:3])[:1500])
    if fn.get('source'):
        lines += ['Source:', '```', fn['source'].rstrip(), '```']
    if fn.get('doc'):
        lines += ['Docstring: ' + fn['doc']]
    body = lean_body(translation, fn)
    if body:
        kind = ('a plain Lean def; `call` decodes the Val arguments, runs it and encodes the result'
                if 'NLModel' in translation.get('call_template', '') else 'Core syntax')
        lines += [f'Its translation into the Lean model ({kind}):', '```lean', body, '```']
    return '\n'.join(lines)


def build_prompt(translation: dict, fn: dict, spec: dict, prop: dict) -> str:
    return '\n'.join([
        'You translate one English property of a program function into a Lean 4 statement about '
        'the function\'s Lean model. You write only three pieces: the binders, a precondition '
        '`pre` and a postcondition `post` (both Lean `Bool` expressions). The harness assembles',
        '  ∀ (a : Int) (b : Int), (pre) = true → (fun (r : EResult) => post) (<call>) = true',
        'where <call> runs the translated function on the binders.',
        VOCABULARY, EXAMPLES, RULES,
        '## The function', describe_function(translation, fn),
        f"Summary of the function: {spec.get('summary', '')}",
        '## The property to formalize',
        f"[{prop.get('kind', 'postcondition')}] {prop['text']}",
        '',
        'Reply with JSON {"binders": [{"name": ..., "type": "Int"|"Bool"|"String"|"Val"}, ...], '
        '"pre": "<Lean Bool>", "post": "<Lean Bool using r>", '
        + ('"observe": "result"|"post", ' if (fn.get('kind') in RECEIVER_KINDS) else '')
        + '"note": "<one line, optional>"}.',
    ])


def repair_prompt(base: str, cand: dict, scratch: str, errors: str) -> str:
    numbered = '\n'.join(f'{i + 1:4d}  {line}' for i, line in enumerate(scratch.splitlines()))
    return (base + '\n\n## Your previous answer was rejected\n'
            + json.dumps({k: cand.get(k) for k in ('binders', 'pre', 'post')}, ensure_ascii=False)
            + '\n\nIt was checked in this Lean file:\n```lean\n' + numbered + '\n```\n'
            + 'Errors:\n```\n' + errors.strip()[:4000] + '\n```\n'
            + 'Fix the pieces so they elaborate while still saying exactly what the English says.')


# ---------------------------------------------------------------- parsing and shape checks

def parse_candidate(data: dict) -> dict:
    """Normalize the model's JSON: binders get their `val`; pre/post become stripped strings."""
    binders = []
    for b in data.get('binders') or []:
        if isinstance(b, dict):
            name, typ = str(b.get('name', '')).strip(), str(b.get('type', '')).strip()
        elif isinstance(b, (list, tuple)) and len(b) >= 2:
            name, typ = str(b[0]).strip(), str(b[1]).strip()
        else:
            name, typ = str(b), ''
        binders.append({'name': name, 'type': typ})
    for b in binders:
        if b['type'] in TYPES and IDENT.match(b['name']):
            b['val'] = binder_val(b)
    pre = str(data.get('pre') if data.get('pre') is not None else 'true').strip() or 'true'
    post = str(data.get('post') or '').strip()
    entry = 'post' if str(data.get('observe') or '').strip().lower() in ('post', 'state') else ''
    return {'binders': binders, 'pre': pre, 'post': post, 'note': str(data.get('note') or ''), 'entry': entry}


def mentions_r(expr: str) -> bool:
    # ignore string literals so `.str "r"` does not count
    return bool(MENTIONS_R.search(re.sub(r'"(?:[^"\\]|\\.)*"', '""', expr)))


def shape_problems(fn: dict, cand: dict, call: str | None = None, lean_prop: str | None = None) -> list:
    """Reasons the candidate is not a usable statement, independent of Lean."""
    problems = []
    params = fn.get('params') or []
    binders = cand['binders']
    if len(binders) != len(params):
        problems.append(f'need exactly {len(params)} binder(s), one per parameter '
                        f'{[p["name"] for p in params]}, got {len(binders)}')
    seen = set()
    for i, b in enumerate(binders):
        if not IDENT.match(b['name']) or b['name'] in KEYWORDS:
            problems.append(f'binder name {b["name"]!r} is not a usable Lean identifier (and `r` is reserved)')
        if b['name'] in seen:
            problems.append(f'duplicate binder name {b["name"]!r}')
        seen.add(b['name'])
        if b['type'] not in TYPES:
            problems.append(f'binder {b["name"]!r} has type {b["type"]!r}; use Int, Bool, String or Val')
        elif i < len(params):
            allowed = SORT_TYPES.get(params[i].get('sort', 'any'))
            if allowed and b['type'] not in allowed:
                problems.append(f'parameter {params[i]["name"]} has sort {params[i]["sort"]}; '
                                f'binder {b["name"]!r} must have type {sorted(allowed)[0]}')
    if cand.get('entry') == 'post' and fn.get('kind') not in RECEIVER_KINDS:
        problems.append('"observe": "post" is only for methods')
    if not cand['post']:
        problems.append('post is empty')
    elif not mentions_r(cand['post']):
        problems.append('post does not inspect the result `r`: the statement would not be about the function')
    if mentions_r(cand['pre']):
        problems.append('pre mentions `r`; the result is only in scope in post')
    if re.fullmatch(r'\(?\s*false\s*\)?', cand['pre']):
        problems.append('pre is `false`: the statement would be vacuous')
    for piece in ('pre', 'post'):
        if re.search(r'\bsorry\b|\badmit\b|\btheorem\b|\baxiom\b|\bby\b', cand[piece]):
            problems.append(f'{piece} must be a plain term (no sorry/admit/theorem/axiom/tactics)')
    if call is not None and lean_prop is not None and call not in lean_prop:
        problems.append('statement does not mention the call')
    return problems


# ---------------------------------------------------------------- Lean

def lake() -> str:
    return shutil.which('lake') or str(Path.home() / '.elan/bin/lake')


def scratch_text(translation: dict, thm: str, cand: dict, lean_prop: str) -> str:
    bs = ' '.join(f"({b['name']} : {b['type']})" for b in cand['binders'])
    pre_fun = f'fun {bs} => ' if bs else ''
    return '\n'.join([
        *[f'import {m}' for m in schema.lean_imports(translation)],
        'open Autoform.Core',
        schema.lean_opens(translation).rstrip(),
        'set_option linter.unusedVariables false',
        '-- pre',
        f"#check {pre_fun}((({cand['pre']})) : Bool)",
        '-- post',
        f"#check fun {bs} (r : EResult) => ((({cand['post']})) : Bool)".replace('fun  ', 'fun '),
        '-- statement',
        f'theorem {thm} : {lean_prop} := by sorry',
        '',
    ])


def run_lean(lean_root: str, path: Path, timeout: int = LEAN_TIMEOUT) -> tuple:
    """(ok, log). ok means Lean exited 0 and reported no error."""
    env = dict(os.environ)
    env['PATH'] = str(Path.home() / '.elan/bin') + os.pathsep + env.get('PATH', '')
    with LEAN_SLOTS:
        try:
            proc = subprocess.run([lake(), 'env', 'lean', str(path)], cwd=lean_root, env=env,
                                  capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return False, f'lean timed out after {timeout}s'
    log = '\n'.join(line for line in (proc.stdout + proc.stderr).splitlines()
                    if 'has local changes' not in line)
    ok = proc.returncode == 0 and not re.search(r'(^|:\s)error:', log, re.M)
    return ok, log


def errors_only(log: str) -> str:
    """Keep error messages (with their continuation lines), drop warnings and #check output."""
    out, keep = [], False
    for line in log.splitlines():
        if re.match(r'^\S+\.lean:\d+:\d+: ', line):
            keep = bool(re.search(r': error(\([^)]*\))?:', line))
        elif re.match(r'^(error|warning):', line):
            keep = line.startswith('error')
        if keep:
            out.append(line)
    return '\n'.join(out) or log[-2000:]


# ---------------------------------------------------------------- one property

def formalize_one(translation: dict, fn: dict, spec: dict, prop: dict, scratch_dir: Path, *,
                  repairs: int = 3, ask=None) -> tuple:
    """Return (Statement, stats dict)."""
    ask = ask or llm.ask_json
    sid = statement_id(fn['name'], prop['id'])
    thm = 'stmt_' + sid
    base = build_prompt(translation, fn, spec, prop)
    prompt, log, cost, t0 = base, [], 0.0, time.time()
    cand = {'binders': [], 'pre': 'true', 'post': ''}
    lean_prop = ''
    ok = False
    attempts = 0
    for attempt in range(repairs + 1):
        attempts = attempt + 1
        try:
            data, c = ask(prompt, ['binders', 'pre', 'post'], cwd=str(scratch_dir))
        except llm.LLMError as exc:
            log.append(f'attempt {attempts}: model error: {exc}')
            break
        cost += c
        cand = with_receiver_guard(fn, parse_candidate(data), translation)
        call = build_call(translation['call_template'], fn['name'] + ('#post' if cand.get('entry') == 'post' else ''),
                          [b.get('val', b['name']) for b in cand['binders']])
        lean_prop = assemble(cand['binders'], cand['pre'], cand['post'], call)
        text = scratch_text(translation, thm, cand, lean_prop)
        path = scratch_dir / f'{sid}.attempt{attempts}.lean'
        path.write_text(text)
        problems = shape_problems(fn, cand, call, lean_prop)
        if problems:
            errors = 'shape check (before Lean):\n' + '\n'.join('- ' + p for p in problems)
        else:
            ok, lean_log = run_lean(translation['lean_root'], path)
            errors = '' if ok else errors_only(lean_log)
        log.append(f'attempt {attempts}: ' + ('elaborates' if ok else 'rejected\n' + errors))
        if ok:
            break
        prompt = repair_prompt(base, cand, text, errors)
    stmt = schema.Statement(
        id=sid, function=fn['name'], property=prop['id'], english=prop['text'],
        lean_prop=lean_prop,
        binders=[{'name': b['name'], 'type': b['type'], 'val': b.get('val', '')} for b in cand['binders']],
        pre=cand['pre'], post=cand['post'], elaborates=ok,
        elaboration_log='\n'.join(log), attempts=attempts, entry=cand.get('entry', ''))
    return stmt, {'id': sid, 'elaborates': ok, 'attempts': attempts, 'cost_usd': cost,
                  'seconds': round(time.time() - t0, 1)}


# ---------------------------------------------------------------- stage entry point

def formalize(translation: dict, english: list, out_dir: Path, *, parallel: int = 3,
              repairs: int = 3, ask=None, budget_usd: float | None = None) -> list:
    """Formalize every English property; write `out_dir/statements.json`.

    `english` is a list of `EnglishSpec` dicts. Properties of functions missing from the
    translation are skipped (recorded in `formalize-stats.json`). With `budget_usd` the
    functions are taken one at a time (their properties in parallel) and no function starts
    once the spend plus the dearest function so far would cross the budget; the properties
    not formalized are named in budget.json with the amount spent at that point."""
    out_dir = Path(out_dir)
    scratch = out_dir / 'scratch'
    scratch.mkdir(parents=True, exist_ok=True)
    by_name = {f['name']: f for f in translation['functions']}
    jobs, skipped = [], []
    for spec in english:
        spec = spec if isinstance(spec, dict) else schema.asdict(spec)
        fn = by_name.get(spec['function'])
        for prop in spec.get('properties', []):
            prop = prop if isinstance(prop, dict) else schema.asdict(prop)
            if fn is None:
                skipped.append({'function': spec['function'], 'property': prop.get('id'),
                                'reason': 'function not in translation'})
            else:
                jobs.append((fn, spec, prop))
    t0 = time.time()
    one = lambda j: formalize_one(translation, *j, scratch, repairs=repairs, ask=ask)  # noqa: E731
    with ThreadPoolExecutor(max_workers=max(1, parallel)) as pool:
        if budget_usd is None:
            results = list(pool.map(one, jobs))
        else:
            groups: dict = {}
            for j in jobs:
                groups.setdefault(j[0]['name'], []).append(j)
            results, over, spent, dearest = [], [], 0.0, 0.0
            for name, js in groups.items():
                if llm.over_budget(spent, budget_usd, dearest):
                    over += [llm.budget_skip(name, spent, budget_usd, dearest, property=j[2].get('id')) for j in js]
                    continue
                got = list(pool.map(one, js))
                results += got
                c = sum(st['cost_usd'] for _, st in got)
                spent, dearest = spent + c, max(dearest, c)
            llm.record_skips(out_dir, 'formalize', over)
            skipped += [dict(function=s['function'], property=s['property'], reason=s['reason']) for s in over]
    statements = [s for s, _ in results]
    stats = [st for _, st in results]
    schema.dump(statements, out_dir / schema.FILES['statements'])
    summary = {
        'statements': len(statements),
        'elaborated': sum(s.elaborates for s in statements),
        'first_try': sum(s.elaborates and s.attempts == 1 for s in statements),
        'after_repair': sum(s.elaborates and s.attempts > 1 for s in statements),
        'failed': sum(not s.elaborates for s in statements),
        'cost_usd': round(sum(st['cost_usd'] for st in stats), 4),
        'seconds': round(time.time() - t0, 1),
        'per_statement': stats, 'skipped': skipped,
    }
    (out_dir / 'formalize-stats.json').write_text(json.dumps(summary, indent=1))
    return statements


def main(argv=None):
    import argparse
    ap = argparse.ArgumentParser(description='English properties -> elaborating Lean statements')
    ap.add_argument('translation')
    ap.add_argument('english')
    ap.add_argument('out_dir')
    ap.add_argument('--parallel', type=int, default=3)
    ap.add_argument('--lean-root', help='override translation.lean_root')
    a = ap.parse_args(argv)
    tr = schema.load(a.translation)
    if a.lean_root:
        tr['lean_root'] = a.lean_root
    stmts = formalize(tr, schema.load(a.english), Path(a.out_dir), parallel=a.parallel)
    print(json.dumps(json.loads((Path(a.out_dir) / 'formalize-stats.json').read_text()),
                     indent=1, default=str)[:3000])
    return 0 if all(s.elaborates for s in stmts) else 1


if __name__ == '__main__':
    raise SystemExit(main())
