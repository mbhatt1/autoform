class Target:
    def __init__(self, value):
        self.value = value

    @staticmethod
    def adjust(value):
        return value + 5

    @classmethod
    def classify(cls, value):
        if cls is Target:
            return value + 7
        return -1

    def invoke(self, value):
        return self.value * 10 + value


def saved_static(value):
    cls = Target
    callback = cls.adjust
    return callback(value)


def static_identity(value):
    target = Target(value)
    cls = Target
    if target.adjust is cls.adjust:
        return value + 1
    return -1


def saved_classmethod(value):
    cls = Target
    callback = cls.classify
    return callback(value)


def saved_unbound(value):
    cls = Target
    callback = cls.invoke
    target = Target(value)
    return callback(target, 3)


def saved_local_static(value):
    offset = value + 10

    class Local:
        @staticmethod
        def adjust(item):
            return item + offset

    cls = Local
    callback = cls.adjust
    return callback(value)
