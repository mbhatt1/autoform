"""Runtime callable bindings whose names collide with inferred static targets."""


class Base:
    __slots__ = ('value',)

    def __init__(self, value):
        self.value = value

    def adjust(self, amount):
        return self.value + amount

    @classmethod
    def owner(cls):
        return cls


class Child(Base):
    __slots__ = ()


def plus(value):
    return value + 10


def saved_classmethod(value):
    owner = Child.owner
    return value if owner() is Child else -1


def saved_instance_classmethod(value):
    owner = Child(value).owner
    return value if owner() is Child else -1


def saved_method(value):
    adjust = Child(value).adjust
    return adjust(value + 1)


def apply_parameter(plus, value):
    return plus(value)


def parameter_collision(value):
    return apply_parameter(Child(value).adjust, value + 1)


def constructor_collision(value):
    Base = plus
    return Base(value)


def captured_method(value):
    adjust = Child(value).adjust

    def inner(amount):
        return adjust(amount)

    return inner(value + 1)


def nonlocal_method(value):
    adjust = Child(value).adjust

    def inner(amount):
        nonlocal adjust
        result = adjust(amount)
        adjust = plus
        return result + adjust(amount)

    return inner(value + 1)


def saved_before_walrus(value):
    adjust = Child(value).adjust
    return adjust((adjust := plus)(value))


def lifted_keyword(value):
    adjust = Child(value).adjust
    return adjust(amount=[x + value for x in [1, 2]][0])


def local_function(value):
    def owner():
        return value + 1

    return owner()


def local_class(value):
    class Local:
        def adjust(self, amount):
            return amount + 1

    return Local().adjust(value)


def builtin_collision(value):
    len = plus
    return len(value)


def callback_factory(value):
    def owner():
        return Child(value).adjust

    return owner()(value + 1)
