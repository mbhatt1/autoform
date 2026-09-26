"""Decorators the program defines, applied when each definition executes.

Language Reference §8.7: `@d1 @d2 def g(...)` binds `g = d1(d2(<function g>))`; the
decorator expressions are evaluated top-down before the function object is created, and
applied bottom-up. `tests/test_python_decorators.py` compares every entry point below
with CPython, and names every refusal.
"""
import functools

trace = []


def twice(f):
    """A plain wrapper."""
    def wrapper(x):
        return f(f(x))
    return wrapper


def add(n):
    """A decorator factory: `@add(n)` evaluates `add(n)` first, then applies it."""
    def deco(f):
        def wrapper(x):
            return f(x) + n
        return wrapper
    return deco


def traced(label):
    """Records when the decorator expression is evaluated and when it is applied."""
    trace.append(label)

    def deco(f):
        trace.append(label + '!')
        return f
    return deco


def negate(x):
    return -x


def replace(f):
    """Returns a different callable altogether."""
    return negate


def add_method(k):
    """A method decorator: the wrapper receives the instance as its first argument."""
    def deco(f):
        def wrapper(self, *args):
            return f(self, *args) + k
        return wrapper
    return deco


def keep(f):
    """Returns the function object it was given."""
    return f


def wraps_deco(f):
    """Defined here, but its wrapper uses the external `functools.wraps`."""
    @functools.wraps(f)
    def wrapper(x):
        return f(x) + 1
    return wrapper


def inc(x):
    return x + 1


before = inc(1)


@twice
def inc(x):
    return x + 1


after = inc(1)


@add(10)
def plain(x):
    return x * 2


@traced('a')
@traced('b')
@twice
def stacked(x):
    return x + 3


@replace
def replaced(x):
    return x + 100


def tag(f):
    def wrapper(x):
        return f(x) + 1000
    return wrapper


@tag
def tagged_first(x):
    return x


tag = add(100)


@tag
def tagged_second(x):
    return x


class Box:
    def __init__(self, v):
        self.v = v

    @add_method(1)
    def value(self, n):
        return self.v + n

    @keep
    def same(self, n):
        return self.v * n


class Holder:
    def _local(f):
        return f

    @_local
    def m(self):
        return 1


def use_inc(x):
    return inc(x)


def use_plain(x):
    return plain(x)


def use_stacked(x):
    return stacked(x)


def use_replaced(x):
    return replaced(x)


def use_rebinding(x):
    return before + after + x


def use_order(x):
    return len(trace) + x if trace[0] + trace[1] + trace[2] + trace[3] == 'abb!a!' else -1


def use_tags(x):
    return tagged_first(x) + tagged_second(x)


def use_local(x):
    @add(x)
    @twice
    def inner(y):
        return y + 1
    return inner(x)


def use_method(x):
    return Box(5).value(x)


def use_bound(x):
    bound = Box(x).value
    return bound(3)


def use_class_attribute(x):
    return Box.value(Box(x), 4)


def use_same(x):
    return Box(x).same(3)


def use_holder(x):
    return Holder().m() + x


def use_wraps(x):
    @wraps_deco
    def inner(y):
        return y
    return inner(x)
