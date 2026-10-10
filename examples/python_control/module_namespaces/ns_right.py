value = 2


def read():
    return value


class Box:
    def __init__(self, value):
        self.value = value + 100
