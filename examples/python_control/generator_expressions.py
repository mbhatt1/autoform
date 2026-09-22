"""Generator-expression creation, resumption and consumer effects."""


class Source:
    def __init__(self, n):
        self.n = n
        self.position = 0
        self.iterations = 0

    def __iter__(self):
        self.iterations += 1
        return self

    def __next__(self):
        if self.position >= self.n:
            raise StopIteration
        self.position += 1
        return self.position


def stored(n):
    generator = (x + 1 for x in [n, n + 1])
    return next(generator) * 10 + next(generator)


def first_iterator(n):
    source = Source(n)
    generator = (x + 1 for x in source)
    before = source.iterations * 100 + source.position * 10
    value = next(generator)
    return before * 100 + source.iterations * 10 + value


def deferred_failure(n):
    generator = (1 // x for x in [0])
    try:
        next(generator)
    except ZeroDivisionError:
        return n
    return 0


def creation_failure(n):
    try:
        generator = (x for x in n)
    except TypeError:
        return n + 1
    return 0


def nested(n):
    generator = (x * 10 + y for x in [n, n + 1] for y in [x, x + 1] if y % 2)
    return sum(generator)


def destructured(n):
    x = 7
    generator = (x + y for x, y in [(n, 1), (n, 2)])
    return sum(generator) * 10 + x


def live_source(n):
    values = [n, n + 1]
    generator = (x for x in values)
    values.append(n + 2)
    return sum(generator)


def collect_list(n):
    values = list(x + 1 for x in [n, n + 1])
    values.append(5)
    return values[0] * 100 + values[1] * 10 + values[2]


def collect_tuple(n):
    values = tuple(x + 1 for x in [n, n + 1])
    return values[0] * 10 + values[1]


def short_any(n):
    return int(any(2 // x for x in [n, 0]))


def short_all(n):
    return int(all(0 // x for x in [n, 0]))


def exhausted_any(n):
    return int(any(x for x in [0, 0])) + n


def exhausted_all(n):
    return int(all(x for x in [1, 2])) + n


def shadow_consumer(n):
    tuple = receive_next
    return tuple(x for x in [n, n + 1])


def receive_next(values):
    return next(values) + 100


def receive_first(values, later):
    return next(values) * 10 + later


def later_argument(n):
    values = [n]
    try:
        return receive_first((x for x in values), values.pop())
    except StopIteration:
        return n + 100


def no_length(n):
    generator = (x for x in [n])
    try:
        return len(generator)
    except TypeError:
        return n + 1


def exhausted(n):
    generator = (x for x in [n])
    first = next(generator)
    return first * 100 + next(generator, 3) * 10 + next(generator, 4)


def returned(n):
    return (x + 1 for x in [n, n + 1])


def consume_returned(n):
    return sum(returned(n))


def stopped():
    raise StopIteration


def pep479(n):
    generator = (stopped() for x in [n])
    try:
        next(generator)
    except RuntimeError:
        return n
    return 0


def captured_cell(n):
    generator = (x + n for x in [1])
    n = 5
    return next(generator)


def custom_length_hint(n):
    return len(list(iter(Source(n))))


def floating_sum(n):
    return sum(x for x in [1.0, 2.0])


def nested_range(n):
    return sum(x + y for x in [n] for y in range(x))
