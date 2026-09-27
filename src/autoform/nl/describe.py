"""Describe stage: Translation → one English specification per function.

    describe(translation, out_dir) -> [EnglishSpec]   and writes out_dir/english.json

For every translated function that is hole-free and call-closed, a language model writes a
one-paragraph summary and 2–6 properties. Each property is ONE testable sentence about the
function's observable behaviour (return value or exception) in terms of its parameters,
tagged with the evidence it rests on. The output is untrusted: the formalize and check
stages decide what, if anything, it is worth.

Functions are sent in batches (BATCH per model call) and the answers are validated item by
item; invalid items are dropped and recorded. Diagnostics (skipped functions, dropped items,
cost, time) go to out_dir/english.meta.json so english.json stays a plain [EnglishSpec].
When the model is unavailable or fails, a deterministic fallback (model="fallback") writes
docstring-first summaries and simple template properties read off the source.
"""
from __future__ import annotations

import json
import os
import re
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict
from pathlib import Path

from . import llm, schema

BATCH = 8
MIN_PROPS, MAX_PROPS = 2, 6
KINDS = ('postcondition', 'precondition', 'exception', 'invariant', 'example')
MAX_SOURCE = 3000
MAX_TESTS = 6
MAX_TEXT = 400
FORBIDDEN = re.compile(r'\b(performance|efficient(ly)?|fast(er)?|slow(er)?|complexity|O\(|log(s|ged|ging)?\b|'
                       r'logger|timing|side[- ]channel|constant[- ]time|memory usage|thread[- ]safe)', re.I)
VAGUE = re.compile(r'\b(correct(ly)? (value|result|output)|as expected|appropriate(ly)?|properly)\b', re.I)

INSTRUCTIONS = """\
You write English specifications of source-code functions. Each specification will later be
formalized as a Lean proposition and tested on concrete inputs, so every property must be
precise and checkable.

For EACH function below produce:
- "summary": one paragraph (2-4 sentences) saying what the function is FOR, i.e. its intended
  behaviour, not a line-by-line paraphrase of the body.
- "properties": between 2 and 6 items, each an object
    {"id": "p1", "text": "...", "kind": "...", "evidence": [...]}
  * "text" is ONE sentence about observable behaviour only: the return value, or the
    exception raised, as a function of the parameters. Call the function by its source name
    with its parameter names, e.g. "For all integers a and b, add(a, b) returns a + b." or
    "If b is 0, quotient(a, b) raises ZeroDivisionError."
  * "kind" is one of: postcondition (relation between inputs and the result),
    precondition (an input condition the function requires/assumes), exception (when it
    raises / fails, and with what), invariant (a relation that holds across calls or all
    inputs, e.g. round-trips, symmetry, idempotence, bounds), example (one concrete call and
    its exact result).
  * "evidence" lists what the property rests on: "docstring", "name", "comments",
    "tests:<location>" (use the location given), "caller:<qualified name>", or
    "implementation". If a property is supported ONLY by reading the body (no docstring,
    name, test or caller supports it), its evidence must be exactly ["implementation"].
Rules:
1. Describe the INTENDED behaviour, grounded in the evidence. Where the body disagrees with
   the docstring, name or tests, follow the evidence and not the body (that is how bugs
   are found). Do not invent requirements with no basis.
2. Every property must be decidable on concrete inputs. Quantify only over the parameters,
   using their sorts: int = unbounded mathematical integers unless an integer_type
   (C width such as int32_t/int) is given, in which case state the range or wrap-around
   behaviour; bool; str. A parameter of sort "any" must be described for the domain its
   tests, docstring or name use, and the sentence must say which domain,
   e.g. "for integers a and b" or "for strings s".
3. Prefer precise relations (equalities, inequalities, bounds, exact exceptions,
   round-trips) over vague ones. Never write "returns the correct value" or "works as
   expected".
4. Include at least one property for every exceptional path visible in the code: each
   raise statement, and each operation that can raise or fail on some inputs (division or
   modulo by zero, indexing, conversion, overflow in C).
5. No properties about performance, logging, timing, memory or side channels.
6. The property must be about THIS function's result, not about the implementation's
   internal steps or local variables.
7. Methods ("kind": "method"/"property") take their receiver as the first parameter (sort
   "object"). State properties in terms of the parameters, the returned value and, for a
   method that changes its receiver ("mutates": true), the receiver's state after the call
   ("after c.push(x), c.peek() returns x", "after d.pop(k), k is not in d"): its instance
   attributes and what they hold. A constructor ("kind": "constructor") returns the new
   object; describe its initial state.
Keys: return one entry per function, using the "key" given for it.
"""


# --- input shaping ----------------------------------------------------------------

def _fi(d) -> dict:
    return d if isinstance(d, dict) else asdict(d)


def _eligible(fn: dict) -> str | None:
    """Reason to skip, or None."""
    if not fn.get('hole_free'):
        return 'not hole_free: ' + ', '.join(map(str, fn.get('holes') or []))[:200]
    if not fn.get('call_closed'):
        return 'not call_closed'
    return None


def _select(functions: list, wanted) -> list:
    if wanted is None:
        return functions
    wanted = set(wanted)
    return [f for f in functions if f['name'] in wanted or f.get('source_name') in wanted
            or f['name'].split('<module>.', 1)[-1] in wanted or f.get('file') in wanted]


def _brief(fn: dict, key: str, language: str) -> dict:
    return dict(
        key=key,
        name=fn['name'],
        call_as=fn.get('source_name') or fn['name'],
        language=language,
        file=f"{fn.get('file', '')}:{fn.get('line') or '?'}",
        params=[dict(name=p['name'], sort=p.get('sort', 'any'),
                     **({'integer_type': p['integer_type']} if p.get('integer_type') else {}))
                for p in fn.get('params') or []],
        returns=fn.get('returns', 'any'),
        needs_init=bool(fn.get('needs_init')),
        **({'kind': fn['kind'], 'receiver': fn.get('receiver', ''), 'mutates': bool(fn.get('mutates'))}
           if fn.get('kind') not in (None, 'function') else {}),
        doc=(fn.get('doc') or '')[:1200],
        tests=[dict(location=t.get('location', ''), text=(t.get('text') or '')[:200])
               for t in (fn.get('tests') or [])[:MAX_TESTS]],
        callers=list(fn.get('callers') or [])[:5],
        source=(fn.get('source') or '')[:MAX_SOURCE],
    )


def prompt_for(batch: list, language: str) -> str:
    items = [_brief(fn, key, language) for key, fn in batch]
    return (INSTRUCTIONS + '\nFunctions (JSON):\n' + json.dumps(items, indent=1, ensure_ascii=False)
            + '\n\nThe answer object has key "functions": a list of '
              '{"key", "summary", "properties"} entries, one per function above.')


# --- validation ---------------------------------------------------------------------

def validate(fn: dict, entry, model: str) -> tuple[schema.EnglishSpec | None, list]:
    """Turn one model entry into an EnglishSpec; return (spec or None, problems)."""
    problems = []
    if not isinstance(entry, dict):
        return None, ['entry is not an object']
    summary = entry.get('summary')
    if not isinstance(summary, str) or not summary.strip():
        problems.append('empty summary')
        summary = ''
    props, seen = [], set()
    raw = entry.get('properties')
    if not isinstance(raw, list):
        return None, problems + ['properties is not a list']
    for i, p in enumerate(raw):
        where = f'property #{i + 1}'
        if not isinstance(p, dict):
            problems.append(f'{where}: not an object'); continue
        pid = str(p.get('id') or '').strip()
        text = p.get('text')
        kind = p.get('kind')
        ev = p.get('evidence')
        if not pid:
            problems.append(f'{where}: missing id'); continue
        if pid in seen:
            problems.append(f'{where}: duplicate id {pid}'); continue
        if not isinstance(text, str) or not text.strip():
            problems.append(f'{pid}: empty text'); continue
        text = ' '.join(text.split())
        if len(text) > MAX_TEXT:
            problems.append(f'{pid}: text longer than {MAX_TEXT} chars'); continue
        if kind not in KINDS:
            problems.append(f'{pid}: kind {kind!r} not in {KINDS}'); continue
        if FORBIDDEN.search(text):
            problems.append(f'{pid}: about performance/logging/side channels'); continue
        if VAGUE.search(text):
            problems.append(f'{pid}: vague ("{VAGUE.search(text).group(0)}")'); continue
        if isinstance(ev, str):
            ev = [ev]
        ev = [str(e).strip() for e in (ev or []) if str(e).strip()] if isinstance(ev, list) else []
        if not ev:
            ev = ['implementation']
        seen.add(pid)
        props.append(schema.EnglishProperty(pid, text, kind, ev))
    if len(props) > MAX_PROPS:
        problems.append(f'{len(props)} properties; kept the first {MAX_PROPS}')
        props = props[:MAX_PROPS]
    if len(props) < MIN_PROPS:
        problems.append(f'only {len(props)} valid properties (want {MIN_PROPS}-{MAX_PROPS})')
    if not props:
        return None, problems
    return schema.EnglishSpec(fn['name'], summary.strip(), props, model), problems


# --- deterministic fallback ---------------------------------------------------------

_SENT = re.compile(r'(?<=[.!?])\s+')


def _domain(fn: dict) -> str:
    params = fn.get('params') or []
    if not params:
        return ''
    names = [p['name'] for p in params]
    sorts = {p.get('sort', 'any') for p in params}
    widths = {p.get('integer_type') or '' for p in params}
    word = {'int': 'integers', 'bool': 'booleans', 'str': 'strings', 'float': 'floats'}
    noun = word.get(sorts.pop(), 'integers') if len(sorts) == 1 else 'values'
    if len(widths) == 1 and '' not in widths:
        noun = f'{widths.pop()} values'
    joined = names[0] if len(names) == 1 else ', '.join(names[:-1]) + ' and ' + names[-1]
    return f'For all {noun} {joined}, '


def _body_lines(source: str) -> list:
    """Header followed by the body's statements (Python lines, or C `;`-separated)."""
    src = re.sub(r'("""|\'\'\')(.*?)\1', '', source, flags=re.S)
    src = re.sub(r'/\*.*?\*/', '', src, flags=re.S)
    src = re.sub(r'//.*$', '', src, flags=re.M)
    if '{' in src and not re.match(r'\s*(async\s+)?def\b', src):
        head, _, rest = src.partition('{')
        rest = rest.rstrip().rstrip(';').rstrip().rstrip('}')
        stmts = [x.strip() for x in re.split(r'[;{}]', rest) if x.strip()]
        return [head.strip()] + stmts
    lines = [re.sub(r'#.*$', '', ln).strip() for ln in src.splitlines()]
    return [ln for ln in lines if ln]


def fallback(fn: dict, language: str = '') -> schema.EnglishSpec:
    name = fn.get('source_name') or fn['name']
    args = ', '.join(p['name'] for p in fn.get('params') or [])
    call = f'{name}({args})'
    doc = ' '.join((fn.get('doc') or '').split())
    summary = (_SENT.split(doc)[0] if doc else
               f'{call} is defined in {fn.get("file") or "the module"}; no documentation is available, '
               'so this description is read off the implementation.')
    props = []

    def add(text, kind, ev):
        props.append(schema.EnglishProperty(f'p{len(props) + 1}', text, kind, ev))

    source = fn.get('source') or ''
    lines = _body_lines(source)
    body = lines[1:] if lines else []
    returns = [ln for ln in body if re.match(r'return\b', ln)]
    dom = _domain(fn)
    # A body that is a single return statement states its own postcondition.
    if len(body) == 1 and returns:
        expr = returns[0][len('return'):].strip().rstrip(';').strip()
        if expr and language == 'c':
            add(f'{dom}{call} returns the value of the C expression `{expr}` '
                '(C integer conversions and wrap-around apply).', 'postcondition', ['implementation'])
        elif expr:
            add(f'{dom}{call} returns {expr}.', 'postcondition', ['implementation'])
    # Guarded raises: `if cond: raise E` (Python) / `if (cond) ... raise`.
    for m in re.finditer(r'if\s+\(?(.+?)\)?\s*:\s*\n\s*raise\s+([A-Za-z_][\w.]*)', source):
        add(f'If {m.group(1).strip()}, {call} raises {m.group(2)}.', 'exception', ['implementation'])
    if not any(p.kind == 'exception' for p in props):
        for m in re.finditer(r'^\s*raise\s+([A-Za-z_][\w.]*)', source, re.M):
            add(f'On some inputs {call} raises {m.group(1)}.', 'exception', ['implementation'])
            break
    # Division by a parameter.
    pnames = {p['name'] for p in fn.get('params') or []}
    if fn.get('source') and not source.lstrip().startswith(('int ', 'long ', 'unsigned ', 'static ')):
        for m in re.finditer(r'(?<![/*])(//|/|%)\s*([A-Za-z_]\w*)\b', source):
            if m.group(2) in pnames:
                add(f'If {m.group(2)} is 0, {call} raises ZeroDivisionError.', 'exception', ['implementation'])
                break
    # Examples from assertion tests: `assert f(...) == v`.
    for t in fn.get('tests') or []:
        m = re.search(r'assert\w*\s*\(?\s*(' + re.escape(name) + r'\(.*?\))\s*==\s*(.+?)\)?\s*$', t.get('text') or '')
        if m and len(props) < MAX_PROPS:
            add(f'{m.group(1)} returns {m.group(2).strip()}.', 'example', ['tests:' + t.get('location', '')])
    if len(props) < MIN_PROPS and fn.get('returns') in ('int', 'bool', 'str', 'float'):
        add(f'{dom}{call} returns a value of type {fn["returns"]}.', 'postcondition', ['implementation'])
    if len(props) < MIN_PROPS and not fn.get('needs_init'):
        add(f'{dom}{"calling" if dom else "Calling"} {call} twice with the same arguments gives the same result.', 'invariant',
            ['implementation'])
    return schema.EnglishSpec(fn['name'], summary, props[:MAX_PROPS], 'fallback')


# --- driver -------------------------------------------------------------------------

def _ask_batch(batch: list, language: str, model: str | None) -> tuple[dict, float, str | None]:
    """Return ({key: entry}, cost, error)."""
    try:
        data, cost = llm.ask_json(prompt_for(batch, language), ['functions'], model=model)
    except llm.LLMError as exc:
        return {}, 0.0, str(exc)
    entries = data.get('functions')
    if not isinstance(entries, list):
        return {}, cost, '"functions" is not a list'
    return {str(e.get('key')): e for e in entries if isinstance(e, dict)}, cost, None


def tests_from(fns: list, test_dirs) -> int:
    """Fill `tests` of functions that have none from lines of the test files in `test_dirs`
    that call them by name (`name(` or `.name(`); returns how many functions got some."""
    from .model import _test_lines
    lines = _test_lines([Path(d) for d in test_dirs or () if Path(d).is_dir()])
    got = 0
    for fn in fns:
        if fn.get('tests') or not fn.get('source_name'):
            continue
        name = fn['source_name']
        if name.startswith('__') and name.endswith('__'):
            continue
        call = re.compile(r'(?<![\w])' + re.escape(name) + r'\s*\(')
        hits = [{'location': loc, 'text': line.strip()[:240]} for loc, line, _ in lines
                if call.search(line) and not re.match(r'\s*def\s', line)][:MAX_TESTS]
        if hits:
            fn['tests'] = hits
            got += 1
    return got


def describe(translation: dict, out_dir: Path, *, functions=None, parallel: int = 4,
             batch_size: int = BATCH, model: str | None = None,
             use_model: bool | None = None, tests=()) -> list:
    """Write out_dir/english.json ([EnglishSpec]) and english.meta.json; return the specs.

    functions: optional names (qualified or source) to restrict to.
    use_model: None = use the CLI when available; False = fallback only.
    tests: extra test directories whose lines calling a function are shown as evidence
    (for functions the translation recorded no test lines for).
    """
    t0 = time.time()
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    language = translation.get('language', '')
    fns = [_fi(f) for f in translation.get('functions') or []]
    if tests:
        tests_from(fns, tests)
    chosen = _select(fns, functions)
    skipped, todo = [], []
    for fn in chosen:
        why = _eligible(fn)
        (skipped.append(dict(function=fn['name'], reason=why)) if why else todo.append(fn))
    if functions is not None:
        missing = set(functions) - {f['name'] for f in chosen} - {f.get('source_name') for f in chosen} \
            - {f['name'].split('<module>.', 1)[-1] for f in chosen} - {f.get('file') for f in chosen}
        skipped += [dict(function=m, reason='not in translation') for m in sorted(missing)]

    if use_model is None:
        use_model = llm.available()
    keyed = [(f'f{i + 1}', fn) for i, fn in enumerate(todo)]
    batches = [keyed[i:i + batch_size] for i in range(0, len(keyed), batch_size)]
    answers, cost, errors = {}, 0.0, []
    if use_model and batches:
        with ThreadPoolExecutor(max_workers=max(1, parallel)) as pool:
            for got, c, err in pool.map(lambda b: _ask_batch(b, language, model), batches):
                answers.update(got)
                cost += c
                if err:
                    errors.append(err)

    specs, issues = [], []
    model_name = model or os.environ.get('AUTOFORM_LLM_MODEL') or 'claude-code'
    for key, fn in keyed:
        spec, problems = None, []
        if key in answers:
            spec, problems = validate(fn, answers[key], model_name)
        elif use_model:
            problems = ['no answer from the model']
        if spec is None:
            spec = fallback(fn, language)
            if use_model:
                problems.append('used deterministic fallback')
        if problems:
            issues.append(dict(function=fn['name'], problems=problems))
        specs.append(spec)

    schema.dump(specs, out_dir / schema.FILES['english'])
    schema.dump(dict(model=model_name if use_model else 'fallback', described=len(specs),
                     skipped=skipped, issues=issues, errors=errors, batches=len(batches),
                     cost_usd=round(cost, 4), seconds=round(time.time() - t0, 1)),
                out_dir / 'english.meta.json')
    return specs


def main(argv=None):
    import argparse
    ap = argparse.ArgumentParser(description='Describe translated functions in English.')
    ap.add_argument('translation', type=Path)
    ap.add_argument('out_dir', type=Path)
    ap.add_argument('--function', action='append')
    ap.add_argument('--parallel', type=int, default=4)
    ap.add_argument('--fallback', action='store_true', help='do not call the model')
    ap.add_argument('--tests', action='append', default=[], help='extra test directory')
    a = ap.parse_args(argv)
    specs = describe(schema.load(a.translation), a.out_dir, functions=a.function,
                     parallel=a.parallel, use_model=False if a.fallback else None, tests=a.tests)
    print(f'{len(specs)} specs -> {a.out_dir / schema.FILES["english"]}')


if __name__ == '__main__':
    main()
