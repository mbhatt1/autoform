"""Preserve Python's jump-based truth contexts in the value-based Core AST.

CPython codegen_jump_if handles BoolOp, Not, and IfExp recursively. Testing a
materialized BoolOp result would test its short-circuit operand a second time.
The ordinary value form stays separate: `not (a and b)` in value position can
perform that second test, while `if not (a and b)` does not.
"""
if __package__:
    from .ast_tools import rewrite_json
else:
    from ast_tools import rewrite_json


def lower_truth_conditions(root):
    """Copy an AST iteratively, keeping value and truth-context forms distinct."""
    predicates = {}
    yes, no = {'k': 'bool', 'v': True}, {'k': 'bool', 'v': False}

    def force(node):
        if node.get('k') == 'bool':
            return node
        return {'k': 'cond', 'c': node, 't': yes, 'e': no}

    def rewrite(node, out):
        key = id(node)
        kind = node.get('k')
        if kind in ('ifte', 'loop', 'cond'):
            out['c'] = predicates[id(node['c'])]
        # Analysis records the original source operations, independently of the
        # executable condition conversion (including in suspended functions).
        if 'analysisBody' in node:
            out['analysisBody'] = node['analysisBody']
        if 'pythonTruthCache' in node:
            state = out['pythonTruthCache']
            raw = {key: value for key, value in out.items() if key != 'pythonTruthCache'}
            predicates[key] = {'k': 'cond',
                'c': {'k': 'binop', 'op': '==', 'a': state, 'b': {'k': 'int', 'v': 0}},
                't': force(raw),
                'e': {'k': 'binop', 'op': '==', 'a': state, 'b': {'k': 'int', 'v': 2}}}
        elif kind == 'binop' and node.get('op') in ('&&', '||'):
            left = predicates[id(node['a'])]
            right = force(predicates[id(node['b'])])
            predicates[key] = {'k': 'cond', 'c': left,
                               't': right if node['op'] == '&&' else yes,
                               'e': no if node['op'] == '&&' else right}
        elif kind == 'unop' and node.get('op') == '!':
            predicates[key] = {'k': 'unop', 'op': '!', 'a': predicates[id(node['a'])]}
        elif kind == 'cond':
            predicates[key] = {'k': 'cond', 'c': predicates[id(node['c'])],
                               't': force(predicates[id(node['t'])]),
                               'e': force(predicates[id(node['e'])])}
        else:
            predicates[key] = out
        return out

    return rewrite_json(root, rewrite, memoize=True)
