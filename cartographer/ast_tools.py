"""Stack-safe traversal of the compiler's JSON trees.

Walks visit dictionary children in reverse insertion order. Rewrites visit them
in insertion order, after their descendants, and never revisit replacement nodes.
"""


def walk(value):
    """Yield dictionaries, preserving the generator pass's historical order."""
    pending = [value]
    while pending:
        current = pending.pop()
        if isinstance(current, dict):
            yield current
            pending.extend(current.values())
        elif isinstance(current, list):
            pending.extend(current)


def rewrite_json(value, rewrite, *, memoize=False):
    """Copy JSON containers and call ``rewrite(original, copy)`` on dictionaries.

    Memoization preserves shared containers and rewrites each once. Without it,
    every occurrence gets its own copy and callback, as in an unshared JSON tree.
    Neither policy mutates the input; callbacks may change their copied node.
    """
    root = [None]
    cache = {}
    pending = [(value, root, 0, False)]
    while pending:
        current, parent, key, ready = pending.pop()
        if ready:
            if isinstance(current, dict):
                parent[key] = rewrite(current, parent[key])
            if memoize:
                cache[id(current)] = parent[key]
        elif not isinstance(current, (dict, list)):
            parent[key] = current
        elif memoize and id(current) in cache:
            parent[key] = cache[id(current)]
        else:
            copied = {} if isinstance(current, dict) else [None] * len(current)
            parent[key] = copied
            pending.append((current, parent, key, True))
            children = current.items() if isinstance(current, dict) else enumerate(current)
            pending.extend((child, copied, name, False) for name, child in reversed(list(children)))
    return root[0]
