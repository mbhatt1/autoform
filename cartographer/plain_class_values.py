#!/usr/bin/env python3
"""Model class-body `NAME = Cls()` attributes whose class is a plain module-level class.

Usage: plain_class_values.py <ast.json> <source-dir> <out.json>

The exporter records a class attribute whose value it cannot evaluate as
`opaque / class-attribute:unmodeled-value`, and Core then holes EVERY read of that name
through an instance, even when the instance's own dictionary holds the name
(`Cache.__size = _DefaultSize()` in cachetools, shadowed by `self.__size = {}`). This pass
turns the attribute into a `stored` class attribute whose value is a fresh instance of the
class, allocated in the module-objects initialiser exactly where the exporter already
allocates `NAME = object()` sentinels. It changes nothing else.

It is a separate pass, not an exporter option, because the exporter's sources are pinned
by every provenance record (scripts/provenance.py): editing them would invalidate the
records of corpora in languages this change does not touch. The pass is conservative; an
attribute it cannot prove plain stays opaque (the hole is kept, never guessed away):

  * the owner class and the constructed class are top-level classes of the same file, the
    constructed class defined first, each bound exactly once in the file;
  * the constructed class has no bases, decorators or keywords, and no construction,
    attribute-access or descriptor hooks (`__new__ __init__ __get__ __set__ __delete__
    __getattr__ __getattribute__ __setattr__ __delattr__ __set_name__ ...`), so an
    instance is not a descriptor: an instance attribute of the same name shadows it and a
    read that misses falls through to the object (Data Model 3.3.2.2);
  * the call has no arguments, and the attribute is assigned once in the owner's body.

The output is deterministic; the exporter's own JSON layout is reproduced byte for byte
(tests/test_plain_class_values.py compares against an exporter run with the same edit).
"""
import ast
import json
import os
import sys

sys.setrecursionlimit(100000)

HOOKS = {'__new__', '__init__', '__init_subclass__', '__set_name__', '__get__', '__set__',
         '__delete__', '__getattr__', '__getattribute__', '__setattr__', '__delattr__',
         '__class_getitem__', '__call__', '__del__'}
UNMODELED = 'class-attribute:unmodeled-value'


def mangle(name, cls):
    if name.startswith('__') and not name.endswith('__'):
        stripped = cls.lstrip('_')
        return '_' + stripped + name if stripped else name
    return name


def bindings(tree, name):
    """How many times `name` is bound anywhere in the file (conservative)."""
    count = 0
    for node in ast.walk(tree):
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            count += node.name == name
        elif isinstance(node, ast.Name):
            count += node.id == name and not isinstance(node.ctx, ast.Load)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            count += any((a.asname or a.name.split('.')[0]) == name for a in node.names)
        elif isinstance(node, (ast.Global, ast.Nonlocal)):
            count += name in node.names
        elif isinstance(node, ast.arg):
            count += node.arg == name
        elif isinstance(node, ast.ExceptHandler):
            count += node.name == name
    return count


def plain_class(tree, owner, call):
    """The constructed class's name when `call` is a provably plain instance, else None."""
    if (not isinstance(call, ast.Call) or not isinstance(call.func, ast.Name)
            or call.args or call.keywords):
        return None
    name = call.func.id
    classes = [s for s in tree.body if isinstance(s, ast.ClassDef) and s.name == name]
    if len(classes) != 1 or bindings(tree, name) != 1:
        return None
    cls = classes[0]
    if cls.lineno >= owner.lineno or cls.bases or cls.keywords or cls.decorator_list:
        return None
    for statement in cls.body:
        if isinstance(statement, ast.FunctionDef):
            if statement.name in HOOKS or statement.decorator_list:
                return None
        elif isinstance(statement, ast.Assign):
            try:
                empty_slots = (len(statement.targets) == 1
                               and isinstance(statement.targets[0], ast.Name)
                               and statement.targets[0].id == '__slots__'
                               and ast.literal_eval(statement.value) in ((), []))
            except (ValueError, SyntaxError):
                empty_slots = False
            if not empty_slots:
                return None
        elif not (isinstance(statement, ast.Pass)
                  or (isinstance(statement, ast.Expr)
                      and isinstance(statement.value, ast.Constant)
                      and isinstance(statement.value.value, str))):
            return None
    return name


def rewrite(functions, source_dir):
    """Edit `functions` in place; return the list of (owner, attribute, constructed class)."""
    edits = []
    for function in functions:
        rows = function.get('classDeclarations')
        file = function.get('file')
        if not rows or not file or not file.endswith('.py'):
            continue
        path = os.path.join(source_dir, file)
        if not os.path.isfile(path):
            continue
        with open(path, encoding='utf-8') as handle:
            tree = ast.parse(handle.read())
        top = {s.name: s for s in tree.body if isinstance(s, ast.ClassDef)}
        for row in rows:
            prefix = file + ':<module>.'
            short = row['name'][len(prefix):] if row['name'].startswith(prefix) else None
            if short is None or short not in top:
                continue
            owner = top[short]
            if bindings(tree, short) != 1:
                continue
            for attribute in row['attributes']:
                if attribute['kind'] != 'opaque' or attribute['value'] != UNMODELED:
                    continue
                assigns = [s for s in owner.body
                           if isinstance(s, (ast.Assign, ast.AnnAssign))
                           and any(isinstance(t, ast.Name)
                                   and mangle(t.id, short) == attribute['name']
                                   for t in (s.targets if isinstance(s, ast.Assign)
                                             else [s.target]))]
                if len(assigns) != 1 or not isinstance(assigns[0], ast.Assign):
                    continue
                constructed = plain_class(tree, owner, assigns[0].value)
                if constructed is None:
                    continue
                attribute['kind'] = 'stored'
                attribute['value'] = '<classattr>' + row['name'] + '.' + attribute['name']
                edits.append((row['name'], short, attribute['name'], constructed))
    if edits:
        init = [f for f in functions if f['name'] == '<module-objects>:<module>']
        if len(init) != 1:
            raise SystemExit('plain_class_values: no unique <module-objects> initialiser')
        node = init[0]['body']
        while node['k'] == 'seq':
            tail = node
            node = node['b']
        if node['k'] != 'skip':
            raise SystemExit('plain_class_values: initialiser does not end in skip')
        spine = None
        for owner_name, short, attr, constructed in edits:
            qualified = '<classattr>' + owner_name + '.' + attr
            pair = [
                {'k': 'setGlobal', 'x': qualified,
                 'e': {'k': 'alloc', 'cls': constructed, 'args': []}},
                {'k': 'setGlobal', 'x': '<classattr>' + short + '.' + attr,
                 'e': {'k': 'name', 'v': qualified}}]
            for statement in pair:
                cell = {'k': 'seq', 'a': statement, 'b': {'k': 'skip'}}
                if spine is None:
                    tail['b'] = cell
                else:
                    spine['b'] = cell
                spine = cell
    return edits


def main(argv):
    if len(argv) != 4:
        print(__doc__)
        return 2
    with open(argv[1], encoding='utf-8') as handle:
        functions = json.load(handle)
    edits = rewrite(functions, argv[2])
    with open(argv[3], 'w', encoding='utf-8') as handle:
        handle.write(json.dumps(functions, indent=1, ensure_ascii=False))
    for owner, _, attr, constructed in edits:
        print('plain_class_values: %s.%s = %s()' % (owner, attr, constructed))
    print('plain_class_values: %d attribute(s) modelled' % len(edits))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
