"""Calling-convention cases whose missing semantics must remain explicit gaps."""


def default_exception(a, ValueError=ValueError):
    try:
        raise ValueError
    except TypeError:
        return a + 1
    except Exception:
        return a


def literal_default(a=17):
    return a


def none_default(a=None):
    return a is None


def keyword_only(*, a):
    return a


def positional_only(a, /):
    return a


def lambda_default(a):
    mapper = lambda value=a: value
    return mapper()


def unused_default_error(a):
    def unused(value=1 // a):
        return value
    return 9


def mutable_default(a, values=[]):
    values.append(a)
    return len(values)


def ordinary(a):
    return a
