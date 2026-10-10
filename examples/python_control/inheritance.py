class Root:
    def __init__(self, value):
        self.value = value

    def choose(self):
        return self.value + 1

    @property
    def reading(self):
        return self.value + 2

    @property
    def shadowed(self):
        return -1

    @classmethod
    def receiver(cls, value):
        if cls is Diamond:
            return value + 3
        return -1

    @staticmethod
    def adjust(value):
        return value + 4


class Left(Root):
    pass


class Right(Root):
    def choose(self):
        return self.value + 10

    def shadowed(self):
        return -2


class Diamond(Left, Right):
    pass


class BadInitializer:
    def __init__(self):
        return 1


class Empty:
    pass


def diamond_method(value):
    obj = Diamond(value)
    return obj.choose()


def saved_inherited_method(value):
    obj = Diamond(value)
    callback = obj.choose
    return callback()


def inherited_property(value):
    obj = Diamond(value)
    return obj.reading


def first_namespace_before_descriptor(value):
    obj = Diamond(value)
    obj.shadowed = value + 20
    return obj.shadowed


def inherited_property_is_readonly(value):
    obj = Diamond(value)
    try:
        obj.reading = 100
    except AttributeError:
        return obj.reading
    return -1


def saved_class_receiver(value):
    cls = Diamond
    callback = cls.receiver
    return callback(value)


def saved_instance_class_receiver(value):
    obj = Diamond(value)
    callback = obj.receiver
    return callback(value)


def inherited_static(value):
    cls = Diamond
    callback = cls.adjust
    return callback(value)


def bad_initializer_return(value):
    try:
        BadInitializer()
    except TypeError:
        return value + 30
    return -1


def default_initializer_arguments(value):
    try:
        Empty(value)
    except TypeError:
        return value + 40
    return -1


def missing_class_attribute(value):
    cls = Diamond
    try:
        return cls.absent
    except AttributeError:
        return value + 50
