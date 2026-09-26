import ns_left
import ns_right
from ns_left import Box as LeftBox
from ns_right import Box as RightBox
from ns_left import read as imported_read

ns_left.original = ns_left.replacement
from ns_left import original as imported_after_change


def observe():
    return ns_left.read(), ns_right.read(), ns_left.bump(), ns_right.read()


def attribute_store():
    ns_left.value = 7
    return ns_left.read(), imported_read(), ns_right.read()


def imported_constructors():
    return LeftBox(3).value, RightBox(3).value


def rebound_callable():
    first = ns_left.invoke()
    second = ns_left.rebind()
    return first, second, ns_left.invoke()


def import_snapshot():
    ns_left.original = ns_left.choice
    return imported_after_change(), ns_left.original()


def private_globals():
    return ns_left.private_globals()
