"""Read nested JSON without consuming one Python/C stack frame per container.

Source AST depth follows the program, not Python's recursion limit. Container
framing uses an explicit stack; the standard JSON decoder still parses every
string, number and literal, preserving its escaping and numeric semantics.
"""
import json
from pathlib import Path
import re


_SPACE = re.compile(r'[ \t\r\n]*').match


def loads(text):
    if not isinstance(text, str):
        raise TypeError('deep_json.loads requires text')
    scalar = json.JSONDecoder().raw_decode
    stack = []

    def error(message, pos):
        raise json.JSONDecodeError(message, text, pos)

    def value(pos):
        pos = _SPACE(text, pos).end()
        char = text[pos:pos + 1]
        if char in ('[', '{'):
            container = [] if char == '[' else {}
            # phase 0: first item or close; 1: required item; 2: comma or close.
            stack.append([container, char, 0])
            return container, pos + 1
        return scalar(text, pos)

    result, pos = value(0)
    while stack:
        frame = stack[-1]
        container, kind, phase = frame
        pos = _SPACE(text, pos).end()
        char = text[pos:pos + 1]
        close = ']' if kind == '[' else '}'
        if phase in (0, 2) and char == close:
            stack.pop()
            pos += 1
            continue
        if phase == 2:
            if char != ',':
                error("Expecting ',' delimiter", pos)
            frame[2] = 1
            pos += 1
            continue
        if kind == '[':
            item, pos = value(pos)
            container.append(item)
        else:
            if char != '"':
                error('Expecting property name enclosed in double quotes', pos)
            key, pos = scalar(text, pos)
            pos = _SPACE(text, pos).end()
            if text[pos:pos + 1] != ':':
                error("Expecting ':' delimiter", pos)
            item, pos = value(pos + 1)
            container[key] = item
        frame[2] = 2
    pos = _SPACE(text, pos).end()
    if pos != len(text):
        error('Extra data', pos)
    return result


def load(path):
    """Load a UTF-8 JSON file by path; no process-wide stack settings are changed."""
    return loads(Path(path).read_text(encoding='utf-8'))


def dict_nodes(root):
    """Visit each object in a JSON tree, including deeply nested AST bodies."""
    pending = [root]
    while pending:
        node = pending.pop()
        if isinstance(node, dict):
            yield node
            pending.extend(reversed(tuple(node.values())))
        elif isinstance(node, list):
            pending.extend(reversed(node))
