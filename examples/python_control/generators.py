"""Suspension, resumption and cleanup probes for the source differential suite."""


def counter(n, effects):
    while n > 0:
        effects.append(n)
        yield n
        n -= 1


def delayed(n):
    effects = []
    gen = counter(n, effects)
    before = len(effects)
    first = next(gen)
    middle = len(effects)
    second = next(gen)
    return before * 1000 + first * 100 + middle * 10 + second


def independent(n):
    effects = []
    a = counter(n, effects)
    b = counter(n + 3, effects)
    return next(a) * 100 + next(b) * 10 + next(a)


def exchange(n):
    value = yield n
    yield value + n


def sending(n):
    gen = exchange(n)
    first = next(gen)
    second = gen.send(n + 1)
    return first * 100 + second * 10 + next(gen, 7)


def rejected_send(n):
    gen = exchange(n)
    try:
        gen.send(5)
    except TypeError:
        return next(gen)
    return -1


def selected(n):
    while n > 0:
        n -= 1
        if n == 3:
            continue
        if n == 1:
            break
        yield n
    yield 9


def branches(n):
    gen = selected(n)
    return next(gen) * 100 + next(gen) * 10 + next(gen)


def drain(n):
    total = 0
    for value in counter(n, []):
        total = total * 10 + value
    return total


def nested(n):
    for value in counter(n, []):
        yield value + 1


def nested_iteration(n):
    total = 0
    for value in nested(n):
        total = total * 10 + value
    return total


def cleanup(n, effects):
    try:
        yield n
        yield n + 1
    finally:
        effects.append(8)


def cleanup_timing(n):
    effects = []
    gen = cleanup(n, effects)
    next(gen)
    a = len(effects)
    next(gen)
    b = len(effects)
    next(gen, 0)
    next(gen, 0)
    return a * 100 + b * 10 + len(effects)


def caught(n):
    try:
        yield n
        raise ValueError()
    except ValueError:
        yield n + 2


def catch_after_yield(n):
    gen = caught(n)
    return next(gen) * 100 + next(gen) * 10 + next(gen, 7)


def failing(n):
    yield n
    raise ValueError()


def closed_after_error(n):
    gen = failing(n)
    first = next(gen)
    try:
        next(gen)
    except ValueError:
        return first * 10 + next(gen, 7)
    return -1


def accidental_stop(n):
    yield n
    raise StopIteration()


def pep479(n):
    gen = accidental_stop(n)
    first = next(gen)
    try:
        next(gen)
    except RuntimeError:
        return first * 10 + next(gen, 7)
    return -1


def unwind(n):
    try:
        yield n
        raise ValueError()
    finally:
        yield n + 1


def suspended_exception(n):
    gen = unwind(n)
    first = next(gen)
    second = next(gen)
    try:
        next(gen)
    except ValueError:
        return first * 100 + second * 10 + next(gen, 7)
    return -1


def returning(n):
    try:
        yield n
        return
    finally:
        yield n + 1


def suspended_return(n):
    gen = returning(n)
    return next(gen) * 100 + next(gen) * 10 + next(gen, 7)


def local_deletion(n):
    value = n
    yield value
    del value
    try:
        yield value
    except UnboundLocalError:
        yield 8


def deleted_local(n):
    gen = local_deletion(n)
    return next(gen) * 10 + next(gen)


def invoke(f, n):
    yield f(n)


def plus_one(n):
    return n + 1


def callable_local(n):
    return next(invoke(plus_one, n))


class Producer:
    def __init__(self, n):
        self.n = n

    def values(self):
        yield self.n
        self.n += 1
        yield self.n


def method_frame(n):
    owner = Producer(n)
    gen = owner.values()
    first = next(gen)
    second = next(gen)
    return first * 100 + second * 10 + owner.n


def delegated(values):
    yield from values


def returned_value(n):
    yield n
    return n + 1


def enclosing(n):
    def captured():
        yield n
    return captured()
