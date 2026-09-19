"""Native argument-binding subjects, without default values."""


def fixed(a, b):
    return (a, b)


def variadic(a, *rest):
    return (a, rest)


def keywords(a, **kw):
    return (a, kw)


def positional(a, /, **kw):
    return (a, kw)


def named(a, *, b):
    return (a, b)


def mixed(a, /, b, *rest, c, **kw):
    return (a, b, rest, c, kw)


def only_keywords(*, a, b):
    return (a, b)


def nothing():
    return ()


def closure_missing(a):
    def inner(b, c):
        return (a, b, c)
    try:
        return inner(a)
    except TypeError:
        return a


class Receiver:
    def method(self, a, *, b):
        return (a, b)
