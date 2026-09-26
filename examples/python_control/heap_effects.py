class Node:
    def __init__(self, value):
        self.value = value
        self.next = None

    def unlink(self):
        old = self.next
        self.next = None
        if old is not None:
            old.value = old.value + 1


class Appender:
    def __init__(self):
        self.values = []

    def append(self, value):
        self.values.append(value)
        return value


def append_alias(left, right):
    left.append(9)
    return right


def fresh_cycle(value):
    result = [value]
    result.append(result)
    return result


def detach(holder):
    old = holder["item"]
    holder["item"] = []
    old.append(8)


def mutate_then_raise(items):
    items.append(4)
    raise ValueError()


def fresh_shared(value):
    items = [value]
    return {"a": items, "b": items}
