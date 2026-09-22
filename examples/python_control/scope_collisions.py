"""Distinct lexical scopes sharing source lines."""


def paired_generators(n):
    left = (x + 1 for x in [n]); right = (y * 2 for y in [n])
    return next(left) * 10 + next(right)


def paired_consumers(n):
    return sum(x for x in [n, n + 1]) + sum(y for y in [n + 2])


def nested_iterables(n):
    values = (x + 1 for x in (y * 2 for y in [n, n + 1]))
    return sum(values)


def paired_lambdas(n):
    left = lambda x: x + 1; right = lambda y: y * 2
    return left(n) * 10 + right(n)


def paired_lists(n):
    left = [x + 1 for x in [n]]; right = [y * 2 for y in [n]]
    return left[0] * 10 + right[0]


def unicode_columns(n):
    label = "é😀"; left = (x + 1 for x in [n]); right = (y * 2 for y in [n])
    return next(left) * 10 + next(right) + len(label)


def unicode_lambdas(n):
    label = "é😀"; left = lambda x: x + 1; right = lambda y: y * 2
    return left(n) * 10 + right(n) + len(label)


def unicode_raise(n):
    try:
        label = "é😀"; raise ValueError
    except ValueError:
        return n + len(label)
