"""Evidence extraction and context construction for one target function.

Ctx(f) = Local(f) ∪ Callers_k(f) ∪ Callees_k(f) ∪ Tests(f) ∪ Docs(f) ∪ Guards(f) ∪ Effects(f)

Evidence is what the generator and the judge may cite. It is never proof.
"""
from __future__ import annotations

import re
from pathlib import Path

TEST_NAME = re.compile(r'(^test_.*|.*_test|.*Test|.*\.test|.*\.spec)\.[A-Za-z]+$')
SOURCE_SUFFIXES = {'.py', '.c', '.h', '.cc', '.cpp', '.java', '.js', '.ts', '.go', '.kt'}
SECURITY_WORDS = re.compile(r'(auth|allow|permit|grant|admin|owner|role|verify|valid|check|sanitiz|'
                            r'escape|secret|token|sign|priv|access|session|login|password)', re.I)
MAX_SNIPPET = 2400


def _definition_line(text: str, name: str) -> int | None:
    pattern = re.compile(r'^\s*(?:async\s+)?(?:def|function|func|fn)\s+' + re.escape(name) + r'\b'
                         r'|^[\w\s\*\(\)<>,:&]*\b' + re.escape(name) + r'\s*\([^;]*\)\s*(\{|$)', re.M)
    m = pattern.search(text)
    return text.count('\n', 0, m.start()) + 1 if m else None


def source_snippet(source: Path | None, fn) -> tuple[str, str | None, str]:
    """(snippet, location, doc) for a function, bounded in size."""
    if not source or not fn.file:
        return '', None, ''
    path = Path(source) / fn.file
    if not path.is_file():
        return '', None, ''
    text = path.read_text(errors='replace')
    line = _definition_line(text, fn.source_name or fn.name)
    if line is None:
        return '', None, ''
    lines = text.splitlines()
    start = line - 1
    # Leading comments belong to the function's documentation.
    doc_lines = []
    j = start - 1
    while j >= 0 and re.match(r'^\s*(#|//|/?\*)', lines[j]):
        doc_lines.insert(0, lines[j].strip())
        j -= 1
    end = start + 1
    indent = len(lines[start]) - len(lines[start].lstrip())
    while end < len(lines) and (not lines[end].strip() or len(lines[end]) - len(lines[end].lstrip()) > indent
                                or lines[end].strip() in ('}', '};')):
        end += 1
        if lines[end - 1].strip() in ('}', '};') and fn.file.endswith(('.c', '.cc', '.cpp', '.java',
                                                                       '.js', '.ts', '.go', '.kt')):
            break
    body = '\n'.join(lines[start:end])
    m = re.search(r'("""|\'\'\')(.*?)\1', body, re.S)
    doc = ' '.join(doc_lines + ([m.group(2).strip()] if m else []))
    return body[:MAX_SNIPPET], f'{fn.file}:{line}', doc


def test_references(source: Path | None, fn, limit=6) -> list:
    if not source:
        return []
    name = fn.source_name or fn.name
    if not name or name.startswith('<'):
        return []
    found = []
    pattern = re.compile(r'\b' + re.escape(name) + r'\s*\(')
    for path in sorted(Path(source).rglob('*')):
        if len(found) >= limit:
            break
        if (not path.is_file() or path.suffix not in SOURCE_SUFFIXES or '.git' in path.parts
                or not (TEST_NAME.match(path.name) or 'tests' in path.parts or 'test' in path.parts)):
            continue
        try:
            text = path.read_text(errors='replace')
        except OSError:
            continue
        for i, line in enumerate(text.splitlines(), 1):
            if pattern.search(line):
                found.append(dict(type='invariant_test' if 'assert' in line else 'test',
                                  location=f'{path.relative_to(source)}:{i}', text=line.strip()[:200]))
                if len(found) >= limit:
                    break
    return found


def guards(fn) -> list:
    """Branches that lead to a raise are explicit assertions about accepted inputs."""
    raising = set(fn.raises)
    out = []
    for br in fn.branches:
        if not br.params:
            continue
        out.append(dict(type='guard', location=br.block, params=br.params,
                        raises=bool(raising), condition=br.condition))
    return out


def context(program, environment, fn, source=None, k=1) -> dict:
    snippet, location, doc = source_snippet(source, fn)
    callers = program.callers(fn.id)
    callees = program.callees(fn.id)
    ext = program.externals(fn.id)
    ev = []
    if location:
        ev.append(dict(type='naming', location=location,
                       text=f'name `{fn.source_name}`' + (' suggests a security decision'
                                                          if SECURITY_WORDS.search(fn.source_name or '') else '')))
    if doc:
        ev.append(dict(type='documentation', location=location, text=doc[:400]))
    for g in guards(fn):
        ev.append(dict(type='guard', location=g['location'], text='branch on ' + ', '.join(g['params'])))
    ev += test_references(source, fn)
    ev += [dict(type='caller', location=program.by_id[c].name, text='calls ' + fn.name)
           for c in callers[:k * 5]]
    return dict(
        target=fn.id, name=fn.name, source_name=fn.source_name, file=fn.file, location=location,
        params=[dict(id=p.id, name=p.name, sort=p.sort, integer_type=p.integer_type) for p in fn.params],
        return_sort=fn.return_sort, body=snippet, doc=doc,
        callers=[program.by_id[c].name for c in callers], callees=[program.by_id[c].name for c in callees],
        externals=[dict(name=n, semantics=environment.summary(n)['semantics']) for n in ext],
        writes=fn.writes, raises=len(fn.raises), holes=len(fn.holes),
        literals=fn.literals, security_relevant=bool(SECURITY_WORDS.search(fn.source_name or '') or
                                                     SECURITY_WORDS.search(doc or '')),
        evidence=ev, coverage=program.coverage(fn.id, environment))
