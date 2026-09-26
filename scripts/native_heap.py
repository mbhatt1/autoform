"""CPython rooted object-graph snapshots with strict function-state encoding."""
import ast
import inspect
import os
import types


def function_state(value, error):
    """Read only canonical function state, without invoking metadata hooks."""
    if value.__closure__:
        raise error('callable-captures')
    attrs = value.__dict__
    if type(attrs) is not dict or attrs:
        raise error('callable-attributes')
    # Python 3.14 can evaluate annotations when __annotations__ is read.
    if getattr(value, '__annotate__', None) is not None:
        raise error('callable-annotations')
    annotations = value.__annotations__
    if type(annotations) is not dict or annotations:
        raise error('callable-annotations')
    defaults, kwdefaults = value.__defaults__, value.__kwdefaults__
    if ((defaults is not None and (type(defaults) is not tuple or defaults)) or
            (kwdefaults is not None and (type(kwdefaults) is not dict or kwdefaults))):
        raise error('callable-default-state')
    parameters = getattr(value, '__type_params__', ())
    if type(parameters) is not tuple or parameters:
        raise error('callable-type-parameters')
    name, qualname = value.__name__, value.__qualname__
    module, doc = value.__module__, value.__doc__
    if (type(name) is not str or type(qualname) is not str or
            (module is not None and type(module) is not str) or
            (doc is not None and type(doc) is not str)):
        raise error('callable-metadata-state')
    code = value.__code__
    # Code objects can be rebuilt with arbitrary co_consts. Immutability of the
    # code object does not make injected mutable constants safe to omit.
    pending, seen = [code], set()
    budget = 10000
    while pending:
        budget -= 1
        if budget < 0:
            raise error('callable-code-state')
        item = pending.pop()
        kind = type(item)
        if any(kind is primitive for primitive in
               (type(None), bool, int, float, complex, str, bytes, type(Ellipsis))):
            continue
        if id(item) in seen:
            continue
        seen.add(id(item))
        if kind is tuple or kind is frozenset:
            pending.extend(item)
        elif kind is types.CodeType:
            names = (item.co_filename, item.co_name, getattr(item, 'co_qualname', item.co_name))
            if any(type(n) is not str for n in names):
                raise error('callable-code-state')
            pending.extend((item.co_consts, item.co_names, item.co_varnames,
                            item.co_freevars, item.co_cellvars))
        else:
            raise error('callable-code-state')
    return (code, name, qualname, module, doc)


def function_identities(funcs, root):
    """Resolve immutable code locations, refusing repeated lexical definitions.

    Mutable __name__/__qualname__ are not evidence of function identity. Decorated
    wrappers and closures without a unique exported location stay unencodable.
    """
    exported = {f['name'] for f in funcs}
    # A decorated definition's code object is the RAW function the decorators received;
    # the exporter keeps it under `<name><undecorated>` (`undecoratedOf` = source name).
    raw_bodies = {f['undecoratedOf']: f['name'] for f in funcs if f.get('undecoratedOf')}
    result = {}
    for rel in {f.get('file', '') for f in funcs} - {''}:
        path = os.path.realpath(os.path.join(root, rel))
        try:
            with open(path, encoding='utf-8') as stream:
                tree = ast.parse(stream.read())
        except (OSError, SyntaxError, UnicodeError):
            continue
        definitions = {}

        def walk(node, prefix='', owner=None, repeated_scope=False):
            for child in ast.iter_child_nodes(node):
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    name = child.name
                    if owner and name.startswith('__') and not name.endswith('__'):
                        name = '_' + owner.lstrip('_') + name
                    qual = prefix + name
                    line = min([child.lineno] + [d.lineno for d in child.decorator_list])
                    definitions.setdefault(qual, []).append((line, not repeated_scope))
                    walk(child, qual + '.', owner, True)
                elif isinstance(child, ast.ClassDef):
                    walk(child, prefix + child.name + '.', child.name, repeated_scope)
                else:
                    walk(child, prefix, owner, repeated_scope or
                         isinstance(child, (ast.For, ast.AsyncFor, ast.While)))
        walk(tree)
        for qual, lines in definitions.items():
            target = rel + ':<module>.' + qual
            target = raw_bodies.get(target, target)
            # A local def or a def inside a loop can produce distinct function
            # objects, even without captures. A Core name cannot represent that
            # identity distinction. Use lexical source nesting, not the mutable
            # function __qualname__, to refuse this boundary.
            if len(lines) == 1 and lines[0][1] and target in exported:
                result[path, lines[0][0]] = target
    return result


def graph_encoder(base, error, max_depth, max_elems):
    class GraphEncoder(base):
        """One identity namespace for mutable containers and plain instances.

        The pre-call snapshot is immutable. Strong references keep even detached
        input objects alive until the final snapshot has been collected. Tuples
        remain value containers; identity of immutable values is not claimed.
        """
        def __init__(self, class_identities=None, function_identities=None):
            # An absent class index (a legacy AST without `classDeclarations`) keeps
            # the legacy short-name identity: Core's own `Obj.cls` is that short name
            # in that mode, so the graph comparison guesses no more than the result
            # comparison already did. Refusing every plain instance instead turned the
            # oracle into a scalar-only check and hid 154 inherited-attribute
            # divergences on cachetools. With metadata present, an unresolved identity
            # is still refused.
            super().__init__(class_identities=class_identities)
            self.function_identities = function_identities or {}
            self.functions = {}
            self.function_objects = {}

        def enc(self, value, depth=0, in_key=False):
            if id(value) in self.byid:
                if in_key:
                    raise error('object-as-dict-key')
                return ('ref', self.byid[id(value)])
            if type(value) is list or type(value) is dict:
                if in_key:
                    raise error('mutable-dict-key')
                if id(value) in self.byid:
                    return ('ref', self.byid[id(value)])
                if depth > max_depth:
                    raise error('depth')
                return ('ref', self.alloc(value, depth))
            if type(value) is types.FunctionType:
                state = function_state(value, error)
                code = state[0]
                name = self.function_identities.get(
                    (os.path.realpath(code.co_filename), code.co_firstlineno))
                if name is None:
                    raise error('callable-source-identity-unresolved')
                # A code location is not an object identity. Module reexecution
                # and FunctionType can also instantiate one code object twice.
                # Retain the first object and refuse a noninjective observation.
                previous_object = self.function_objects.setdefault(name, value)
                if previous_object is not value:
                    raise error('callable-source-identity-collision')
                previous = self.functions.setdefault(id(value), (value, state))
                if previous[1][0] is not code or previous[1][1:] != state[1:]:
                    raise error('callable-state-changed')
                return ('fn', name)
            if inspect.isroutine(value):
                raise error('bound-or-native-callable-state')
            return super().enc(value, depth, in_key)

        def cell(self, obj, depth):
            if type(obj) is list:
                if len(obj) > max_elems:
                    raise error('wide')
                return ('list', [], ('list', [self.enc(v, depth + 1) for v in obj]))
            if type(obj) is dict:
                if len(obj) > max_elems:
                    raise error('wide')
                return ('dict', [], ('dict', [(self.enc(k, depth + 1, True),
                                              self.enc(v, depth + 1))
                                             for k, v in obj.items()]))
            name, fields = self.object_fields(obj)
            return (name, [(k, self.enc(v, depth + 1)) for k, v in fields.items()], None)

        def alloc(self, obj, depth):
            if id(obj) in self.byid:
                return self.byid[id(obj)]
            if len(self.heap) >= max_elems:
                raise error('wide-heap')
            idx = len(self.heap)
            self.byid[id(obj)] = idx
            self.objs[idx] = obj
            self.heap.append(None)
            self.heap[idx] = self.cell(obj, depth)
            return idx

        def freeze(self):
            super().freeze()
            self.heap = list(self.heap)

        def enc_result(self, value):
            return self.enc(value)

        def post_state(self):
            # Functions are code identities in Core. Do not discard a change to
            # an input function that the stored graph cannot represent.
            for fn, _ in list(self.functions.values()):
                self.enc(fn)
            # Rebuild every retained node, including input nodes detached during
            # the call. Newly discovered nodes extend the same work queue.
            self.heap = [None] * len(self.objs)
            index = 0
            while index < len(self.objs):
                self.heap[index] = self.cell(self.objs[index], 0)
                index += 1
            return self.heap

    return GraphEncoder


def validate_records(rows, report, funcs):
    """Do not upgrade old reports or downgrade a missing graph to return-only."""
    graph_basis = 'heap-graph-v1' in str(report.get('measurement_basis', '')).split('+')
    names = {f['name'] for f in funcs}
    names.update(row['name'] + '<meta>' for f in funcs
                 for row in f.get('classDeclarations', []))

    def fail():
        raise ValueError('invalid or incomplete native heap graph evidence')

    def value(v, size, depth=0):
        if depth > 64 or not isinstance(v, (list, tuple)) or not v:
            fail()
        tag = v[0]
        if tag == 'unit' and len(v) == 1:
            return
        if len(v) != 2:
            fail()
        data = v[1]
        if tag == 'ref':
            if type(data) is not int or not 0 <= data < size:
                fail()
        elif tag == 'fn':
            if data not in names:
                fail()
        elif tag == 'int':
            if type(data) is not int:
                fail()
        elif tag == 'float':
            if type(data) is not int or not 0 <= data < 2**64:
                fail()
        elif tag == 'bool':
            if type(data) is not bool:
                fail()
        elif tag == 'str':
            if type(data) is not str:
                fail()
        elif tag in ('list', 'tuple', 'dict'):
            if not isinstance(data, (list, tuple)):
                fail()
            for item in data:
                if tag == 'dict':
                    if not isinstance(item, (list, tuple)) or len(item) != 2:
                        fail()
                    value(item[0], size, depth + 1)
                    value(item[1], size, depth + 1)
                else:
                    value(item, size, depth + 1)
        else:
            fail()

    def heap(cells):
        if not isinstance(cells, (list, tuple)):
            fail()
        for cell in cells:
            if not isinstance(cell, (list, tuple)) or len(cell) != 3:
                fail()
            cls, fields, payload = cell
            if not isinstance(cls, str) or not isinstance(fields, (list, tuple)):
                fail()
            seen = set()
            for field in fields:
                if not isinstance(field, (list, tuple)) or len(field) != 2:
                    fail()
                name, val = field
                if not isinstance(name, str) or name in seen:
                    fail()
                seen.add(name)
                value(val, len(cells))
            if payload is not None:
                if (cls not in ('list', 'dict') or fields or
                        not isinstance(payload, (list, tuple)) or len(payload) != 2
                        or payload[0] != cls):
                    fail()
                value(payload, len(cells))

    for row in rows:
        if ('post_heap' in row) != graph_basis:
            fail()
        if not graph_basis:
            continue
        if row.get('runtime', report.get('runtime')) != 'cpython':
            fail()
        before, after = row.get('heap'), row.get('post_heap')
        heap(before)
        heap(after)
        if len(after) < len(before):
            fail()
        if row.get('self') is not None:
            value(row['self'], len(before))
        for arg in row.get('args', []):
            value(arg, len(before))
        outcome = row.get('outcome')
        if not isinstance(outcome, (list, tuple)) or len(outcome) != 2:
            fail()
        if outcome[0] == 'val':
            value(outcome[1], len(after))
        elif outcome[0] != 'exn' or not isinstance(outcome[1], str):
            fail()
