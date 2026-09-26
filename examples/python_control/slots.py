"""Slot storage, inheritance, descriptor precedence and rejected assignments."""


class Cell:
    __slots__ = ('value', '__hidden')

    def __init__(self, value):
        self.value = value
        self.__hidden = value + 3

    def hidden(self):
        return self.__hidden


class Empty:
    __slots__ = ()


class Child(Cell):
    __slots__ = ('extra',)


class DictChild(Cell):
    pass


class ExplicitDict(Cell):
    __slots__ = ('__dict__',)


class Mixed(Cell, Empty):
    __slots__ = ()


class Single:
    __slots__ = 'item'


class WithProperty(Cell):
    __slots__ = ()

    @property
    def doubled(self):
        return self.value * 2


def slot_read(value):
    return Cell(value).value


def slot_write(value):
    cell = Cell(value)
    cell.value = value + 4
    return cell.value


def private_slot(value):
    return Cell(value).hidden()


def inherited_slot(value):
    cell = Child(value)
    cell.extra = value + 7
    return cell.value + cell.extra


def subclass_dictionary(value):
    cell = DictChild(value)
    cell.extra = value + 9
    return cell.value + cell.extra


def explicit_dictionary(value):
    cell = ExplicitDict(value)
    cell.extra = value + 11
    return cell.value + cell.extra


def empty_slot_mixin(value):
    return Mixed(value).hidden()


def string_slot(value):
    cell = Single()
    cell.item = value
    return cell.item


def missing_slot(value):
    cell = Single()
    try:
        return cell.item
    except AttributeError:
        return value + 13


def rejected_new_field(value):
    cell = Cell(value)
    try:
        cell.extra = value
    except AttributeError:
        return cell.value
    return -1


def rejected_method_shadow(value):
    cell = Cell(value)
    try:
        cell.hidden = value
    except AttributeError:
        return cell.hidden()
    return -1


def slot_property(value):
    return WithProperty(value).doubled
