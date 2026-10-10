value = 1


def read():
    return value


def bump():
    global value
    value += 1
    return value


def original():
    return 10


def replacement():
    return 20


choice = original


def invoke():
    return choice()


def rebind():
    global choice
    choice = replacement
    return invoke()


class Box:
    def __init__(self, value):
        self.value = value


_PrivateWriter__counter = 0


class PrivateWriter:
    def put(self):
        global __counter
        __counter += 3
        return __counter


def private_globals():
    return PrivateWriter().put(), _PrivateWriter__counter
