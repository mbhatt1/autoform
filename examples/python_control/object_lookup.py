"""Attribute lookup order and binding probes for the source conformance gate."""


def plus_five(value):
    return value + 5


def plus_twenty(value):
    return value + 20


class Noise:
    def callback(self, value):
        return -900


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

    @staticmethod
    def static(value):
        return value + 40

    @classmethod
    def class_method(cls, value):
        return value + 50


def unrelated_method(value):
    target = Target()
    return target.callback(value)


def shadow_method(value):
    target = Target()
    target.invoke = plus_five
    return target.invoke(value)


def saved_field(value):
    target = Target()
    return target.callback(target.change_callback())


def saved_method(value):
    target = Target()
    return target.invoke(target.change_method())


def property_order(value):
    target = Target()
    result = target.selected(target.argument())
    return result * 100 + target.trace


def property_exception(value):
    target = Target()
    try:
        target.fails(target.argument())
    except ValueError:
        return target.trace
    return -1


def missing_before_argument(value):
    target = Target()
    try:
        target.absent(target.argument())
    except AttributeError:
        return target.trace
    return -1


def static_method(value):
    target = Target()
    return target.static(value)


def class_method(value):
    target = Target()
    return target.class_method(value)


def captured_bound_method(value):
    class Local:
        def callback(self, other):
            return value + other
    target = Local()
    callback = target.callback
    return callback(7)


def captured_method_call(value):
    class Local:
        def callback(self, other):
            return value + other
    target = Local()
    return target.callback(7)


def captured_property(value):
    class Local:
        @property
        def selected(self):
            return value + 8
    target = Local()
    return target.selected


def captured_static_method(value):
    class LocalStatic:
        @staticmethod
        def callback(other):
            return value + other
    target = LocalStatic()
    return target.callback(9)
