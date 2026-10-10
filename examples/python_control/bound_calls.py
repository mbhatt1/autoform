"""Bound builtin methods and callable lookup before lifted argument statements."""


def plus_five(value):
    return value + 5


def plus_twenty(value):
    return value + 20


class Target:
    def __init__(self):
        self.callback = plus_five
        self.trace = 0

    def invoke(self, value):
        return value + 100

    def change_callback(self):
        self.callback = plus_twenty
        return 3

    def change_method(self):
        self.invoke = plus_twenty
        return 3

    def argument(self):
        self.trace = self.trace * 10 + 2
        return 3

    @property
    def selected(self):
        self.trace = self.trace * 10 + 1
        return plus_five

    @property
    def fails(self):
        self.trace = self.trace * 10 + 1
        raise ValueError


def property_comprehension(value):
    target = Target()
    result = target.selected([target.argument() for item in [0]][0])
    return result * 100 + target.trace


def property_keyword(value):
    target = Target()
    result = target.selected(value=[target.argument() for item in [0]][0])
    return result * 100 + target.trace


def saved_field_comprehension(value):
    target = Target()
    return target.callback([target.change_callback() for item in [0]][0])


def saved_method_walrus(value):
    target = Target()
    return target.invoke(value := target.change_method())


def missing_comprehension(value):
    target = Target()
    try:
        target.absent([target.argument() for item in [0]][0])
    except AttributeError:
        return target.trace
    return -1


def raising_comprehension(value):
    target = Target()
    try:
        target.fails([target.argument() for item in [0]][0])
    except ValueError:
        return target.trace
    return -1


def saved_append(value):
    items = [1]
    append = items.append
    alias = items
    items = [99]
    append(value)
    return len(alias) * 100 + alias[1] * 10 + len(items)


def append_comprehension(value):
    items = []
    items.append([item + value for item in [1, 2]])
    return len(items) * 100 + items[0][0] * 10 + items[0][1]


def saved_pop(value):
    items = [1, 2, 3]
    pop = items.pop
    return pop() * 10 + pop()


def saved_get(value):
    values = {1: 3}
    get = values.get
    values[1] = 9
    return get(1)


def saved_clear(value):
    values = {1: 3}
    clear = values.clear
    clear()
    return len(values)


def saved_next(value):
    iterator = iter([1, 2])
    step = iterator.__next__
    return step() * 10 + step()
