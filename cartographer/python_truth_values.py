"""Retain an evaluated truth result across nested Python Boolean value operators.

Internal helpers return (value, state), where 0 means untested, 1 means false,
and 2 means true. A short circuit returns its cached result; a final operand
stays untested. Materializing a value discards this cache, so a later independent
truth test still runs the protocol again.
"""


def _lower_function(function):
    body = function['body']
    nodes, pairs, helpers = {}, {}, []
    changed = False
    pending = [(body, False)]

    def name(v):
        return {'k': 'name', 'v': v}

    def integer(v):
        return {'k': 'int', 'v': v}

    def index(a, n):
        return {'k': 'index', 'a': a, 'b': integer(n)}

    def assign(x, e):
        return {'k': 'assign', 'x': x, 'e': e}

    def seq(statements):
        result = statements[-1]
        for statement in reversed(statements[:-1]):
            result = {'k': 'seq', 'a': statement, 'b': result}
        return result

    def eq(a, n):
        return {'k': 'binop', 'op': '==', 'a': a, 'b': integer(n)}

    def pair(child):
        state = nodes[id(child)].get('pythonTruthCache', integer(0))
        return pairs.get(id(child), {'k': 'tupleE', 'items': [nodes[id(child)], state]})

    while pending:
        node, ready = pending.pop()
        if not isinstance(node, (dict, list)) or id(node) in nodes:
            continue
        children = list(node.values()) if isinstance(node, dict) else node
        if not ready:
            pending.append((node, True))
            pending.extend((child, False) for child in reversed(children)
                           if isinstance(child, (dict, list)))
            continue
        if isinstance(node, list):
            nodes[id(node)] = [nodes.get(id(child), child) for child in node]
            continue
        out = {key: nodes.get(id(child), child) for key, child in node.items()}
        nodes[id(node)] = out
        if node.get('k') != 'binop' or node.get('op') not in ('&&', '||'):
            continue
        helper_name = function['name'] + '<truth:' + str(len(helpers)) + '>'
        # These cannot collide with Python identifiers or the exporter's temporaries.
        saved, value, state, tested = (helper_name + suffix for suffix in (':pair', ':value', ':state', ':test'))
        left, val, flag = name(saved), name(value), name(state)
        helper_body = seq([
            assign(saved, pair(node['a'])),
            assign(value, index(left, 0)),
            assign(state, index(left, 1)),
            {'k': 'ifte', 'c': eq(flag, 0),
             't': seq([assign(tested, {'k': 'call', 'f': '<python-bool>', 'args': [val]}),
                       assign(state, {'k': 'cond', 'c': name(tested), 't': integer(2), 'e': integer(1)})]),
             'e': {'k': 'skip'}},
            {'k': 'ifte', 'c': eq(flag, 1 if node['op'] == '&&' else 2),
             't': {'k': 'ret', 'e': {'k': 'tupleE', 'items': [val, flag]}},
             'e': {'k': 'ret', 'e': pair(node['b'])}},
        ])
        helpers.append({'name': helper_name, 'file': function.get('file', ''),
                        'params': [], 'body': helper_body})
        call = {'k': 'callV', 'f': {'k': 'closure', 'f': helper_name}, 'args': []}
        pairs[id(node)] = call
        # Simple binary operators already evaluate their left exactly once. Only
        # a compound left operand needs a cached result from the helper protocol.
        if id(node['a']) in pairs or 'pythonTruthCache' in node['a']:
            nodes[id(node)] = index(call, 0)
            changed = True
    if not changed:
        return function, []
    out = dict(function, body=nodes[id(body)])
    out.setdefault('analysisBody', body)
    # Helpers are auxiliary implementation code, never source-function subjects.
    return out, helpers


def lower_truth_values(functions):
    result = []
    for function in functions:
        source, helpers = _lower_function(function)
        generators = []
        for generator in function.get('generatorHelpers', []):
            lowered, nested = _lower_function(generator)
            generators.append(lowered)
            helpers.extend(nested)
        source = dict(source)
        if generators:
            source['generatorHelpers'] = generators
        if helpers:
            source['truthHelpers'] = helpers
        result.append(source)
    return result
