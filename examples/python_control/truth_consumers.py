"""Consumers must execute truth slots between resumptions and retain their effects."""


def bool(value):
    # Implicit truth testing does not read this source binding.
    return False


class Truth:
    def __init__(self, value, log):
        self.value = value
        self.log = log

    def __bool__(self):
        self.log.append(self.value)
        return self.value != 0

    def __len__(self):
        raise RuntimeError


class Length:
    def __init__(self, value, log):
        self.value = value
        self.log = log

    def __len__(self):
        self.log.append(self.value)
        return self.value


class BadTruth:
    def __bool__(self):
        return 1


class RaisingTruth:
    def __bool__(self):
        raise ValueError


class AppendTruth:
    def __init__(self, values):
        self.values = values

    def __bool__(self):
        self.values.append(1)
        return False


def truth_values(log, first, second):
    yield Truth(first, log)
    yield Truth(second, log)
    yield Truth(7, log)


def nested_values(log):
    log.append(1)
    yield []
    log.append(2)
    yield [1]


def any_generator(n):
    log = []
    values = truth_values(log, 0, n)
    result = any(values)
    following = next(values)
    return int(result) * 100 + len(log) * 10 + following.value


def all_generator(n):
    log = []
    values = truth_values(log, n, 0)
    result = all(values)
    following = next(values)
    return int(result) * 100 + len(log) * 10 + following.value


def any_nested(n):
    log = []
    result = any(nested_values(log))
    return int(result) * 100 + len(log) * 10 + n


def all_nested(n):
    log = []
    result = all(nested_values(log))
    return int(result) * 100 + len(log) * 10 + n


def list_objects(n):
    log = []
    result = any([Truth(0, log), Truth(n, log), Truth(9, log)])
    return int(result) * 100 + len(log) * 10


def tuple_objects(n):
    log = []
    result = all((Truth(n, log), Truth(0, log), Truth(9, log)))
    return int(result) * 100 + len(log) * 10


def length_objects(n):
    log = []
    result = any((Length(0, log), Length(n, log)))
    return int(result) * 100 + len(log) * 10


def boolean_length(n):
    log = []
    return int(all((Length(True, log),))) + n


def negative_length(n):
    log = []
    try:
        any((Length(-1, log),))
    except ValueError:
        return len(log) + n
    return 0


def invalid_truth(n):
    try:
        any((BadTruth(),))
    except TypeError:
        return n
    return 0


def raising_values():
    yield RaisingTruth()
    yield 9


def raised_truth_leaves_generator_open(n):
    values = raising_values()
    try:
        any(values)
    except ValueError:
        return next(values) + n
    return 0


def mutation_during_truth(n):
    values = []
    values.append(AppendTruth(values))
    return int(any(values)) * 100 + len(values) * 10 + n


def plain_containers(n):
    return int(any(([], {}, (), ""))) + int(all(([],))) + int(any("é")) + int(all(())) + n


def invalid_iterable(n):
    try:
        all(n)
    except TypeError:
        return n
    return 0


class PlainObject:
    pass


def unknown_truth(n):
    return int(any((PlainObject(),))) + n


def platform_length(n):
    return int(any((Length(1099511627776, []),))) + n
