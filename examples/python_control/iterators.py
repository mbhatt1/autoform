"""Stateful iterator probes compared with CPython by test_source_iterators.py."""


def list_live(n):
    values = [n, n + 1]
    iterator = iter(values)
    first = next(iterator)
    values.append(n + 2)
    return first * 100 + next(iterator) * 10 + next(iterator)


def list_shrink(n):
    values = [n, n + 1, n + 2]
    iterator = iter(values)
    first = next(iterator)
    del values[0]
    return first * 100 + next(iterator) * 10 + next(iterator, 7)


def exhaustion(n):
    values = [n]
    iterator = iter(values)
    first = next(iterator)
    end = next(iterator, 7)
    values.append(9)
    return first * 100 + end * 10 + next(iterator, 8)


def iterator_identity(n):
    iterator = iter([n])
    if iter(iterator) is iterator and iterator.__iter__() is iterator:
        return iterator.__next__()
    return -1


def direct_container_method(n):
    values = [n]
    iterator = values.__iter__()
    values.append(n + 1)
    return next(iterator) * 10 + next(iterator)


def tuples(n):
    iterator = iter((n, n + 1))
    return next(iterator) * 100 + next(iterator) * 10 + next(iterator, 7)


def unicode_characters(n):
    iterator = iter("Aé𝛼")
    return ord(next(iterator)) + ord(next(iterator)) + ord(next(iterator)) + n


def none_item(n):
    iterator = iter([None, n])
    if next(iterator, 7) is None:
        return next(iterator)
    return -1


def dict_values(n):
    values = {n: 10, n + 1: 20}
    iterator = iter(values)
    first = next(iterator)
    values[n + 1] = 90
    return first * 100 + next(iterator) * 10 + next(iterator, 7)


def dict_value_loop(n):
    values = {n: 10, n + 1: 20}
    total = 0
    for key in values:
        values[key] += 1
        total += values[key]
    return total


def dict_size_error(n):
    values = {n: 10}
    iterator = iter(values)
    values[n + 1] = 20
    try:
        next(iterator)
    except RuntimeError:
        del values[n + 1]
        try:
            next(iterator)
        except RuntimeError:
            return 7
    return -1


def dict_exhaustion(n):
    values = {n: 10}
    iterator = iter(values)
    first = next(iterator)
    end = next(iterator, 7)
    values[n + 1] = 20
    return first * 100 + end * 10 + next(iterator, 8)


class Sequence:
    def __init__(self, n):
        self.n = n
        self.calls = 0

    def __getitem__(self, index):
        self.calls += 1
        if index >= 2:
            raise IndexError()
        return self.n + index


def sequence(n):
    owner = Sequence(n)
    iterator = iter(owner)
    before = owner.calls
    first = next(iterator)
    second = next(iterator)
    next(iterator, 0)
    next(iterator, 0)
    return before * 1000 + first * 100 + second * 10 + owner.calls


class InvalidIterator:
    def __iter__(self):
        return [1, 2]


def invalid_iter(n):
    try:
        iter(InvalidIterator())
    except TypeError:
        return n
    return -1


def invalid_for(n):
    try:
        for value in InvalidIterator():
            return -1
    except TypeError:
        return n
    return -2


class Ticker:
    def __init__(self):
        self.n = 0

    def take(self):
        self.n += 1
        return self.n


def sentinel(n):
    owner = Ticker()
    iterator = iter(owner.take, 3)
    before = owner.n
    first = next(iterator)
    second = next(iterator)
    next(iterator, 0)
    next(iterator, 0)
    return before * 1000 + first * 100 + second * 10 + owner.n + n


def saved_callback(n):
    owner = Ticker()
    take = owner.take
    iterator = iter(take, 3)
    return next(iterator) * 100 + next(iterator) * 10 + next(iterator, 7)


class Sentinel:
    def __init__(self, limit):
        self.limit = limit
        self.comparisons = 0

    def __eq__(self, value):
        self.comparisons += 1
        return value == self.limit


def sentinel_comparison(n):
    owner = Ticker()
    marker = Sentinel(2)
    iterator = iter(owner.take, marker)
    first = next(iterator)
    second = next(iterator, 9)
    third = next(iterator, 8)
    return first * 10000 + second * 1000 + third * 100 + marker.comparisons * 10 + owner.n


class SameValue:
    def __init__(self):
        self.calls = 0

    def take(self):
        self.calls += 1
        return self

    def __eq__(self, other):
        raise ValueError()


def sentinel_identity(n):
    owner = SameValue()
    iterator = iter(owner.take, owner)
    return next(iterator, 7) * 100 + next(iterator, 8) * 10 + owner.calls


class RetriedSequence:
    def __init__(self):
        self.calls = 0

    def __getitem__(self, index):
        self.calls += 1
        if self.calls == 1:
            raise ValueError()
        if index == 1:
            raise StopIteration()
        return index + 3


def sequence_retry(n):
    owner = RetriedSequence()
    iterator = iter(owner)
    try:
        next(iterator)
    except ValueError:
        pass
    first = next(iterator)
    return first * 1000 + next(iterator, 7) * 100 + next(iterator, 8) * 10 + owner.calls


def iterator_for(n):
    iterator = iter([n, n + 1, n + 2])
    first = next(iterator)
    total = 0
    for value in iterator:
        total += value
    return first * 100 + total * 10 + next(iterator, 9)


def nested_dicts(n):
    total = 0
    for a in {n: 1, n + 1: 2}:
        for b in {1: 3, 2: 4}:
            total += a * 10 + b
    return total


def nested_iterators(n):
    total = 0
    for a in iter([n, n + 1]):
        for b in iter([1, 2]):
            total += a * 10 + b
    return total


def nested_sequences(n):
    total = 0
    for a in Sequence(n):
        for b in Sequence(1):
            total += a * 10 + b
    return total


class Reentrant:
    def __init__(self):
        self.calls = 0

    def take(self):
        self.calls += 1
        if self.calls == 1:
            next(self.iterator, 0)
            return 2
        return 3


def sentinel_reentrant(n):
    owner = Reentrant()
    iterator = iter(owner.take, 3)
    owner.iterator = iterator
    return next(iterator, 7) * 100 + next(iterator, 8) * 10 + owner.calls


class Stopping:
    def __init__(self):
        self.calls = 0

    def take(self):
        self.calls += 1
        if self.calls == 1:
            raise ValueError()
        raise StopIteration()


def sentinel_retry(n):
    owner = Stopping()
    iterator = iter(owner.take, 3)
    try:
        next(iterator)
    except ValueError:
        pass
    return next(iterator, 7) * 100 + next(iterator, 8) * 10 + owner.calls


class ClassCallback:
    @classmethod
    def take(cls):
        return 3


class StaticCallback:
    @staticmethod
    def take():
        return 3


def sentinel_classmethod(n):
    owner = ClassCallback()
    return next(iter(owner.take, 3), 7)


def sentinel_staticmethod(n):
    owner = StaticCallback()
    return next(iter(owner.take, 3), 7)


def iter_noniterable(n):
    try:
        iter(n)
    except TypeError:
        return 7
    return -1


def next_noniterator(n):
    try:
        next([n], 9)
    except TypeError:
        return 7
    return -1


def yielded(values):
    for value in values:
        yield value


def generator_list(n):
    values = [n, n + 1]
    generator = yielded(values)
    first = next(generator)
    values.append(n + 2)
    return first * 100 + next(generator) * 10 + next(generator)


def generator_dict(n):
    values = {n: 10, n + 1: 20}
    generator = yielded(values)
    first = next(generator)
    values[n + 1] = 90
    return first * 100 + next(generator) * 10 + next(generator, 7)


def changed_dict_keys(n):
    values = {n: 10, n + 1: 20}
    iterator = iter(values)
    del values[n + 1]
    values[n + 2] = 30
    return next(iterator)


def private_fields(n):
    return getattr(iter([n]), "<index>", 8)


class UnknownResult:
    pass


class UncertainIterator:
    def __iter__(self):
        return UnknownResult()


def result_protocol(n):
    return iter(UncertainIterator())


def result_protocol_for(n):
    for value in UncertainIterator():
        return n
    return -1
