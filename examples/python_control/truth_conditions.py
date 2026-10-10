"""Truth protocols in control flow, operators, and comparison results."""
class Truth:
    def __init__(self, log, value):
        self.log = log
        self.value = value

    def __bool__(self):
        self.log.append(self.value)
        return self.value > 0

    def __len__(self):
        raise RuntimeError()

class Countdown:
    def __init__(self, n):
        self.n = n
        self.calls = 0

    def __len__(self):
        self.calls += 1
        return self.n

class Raising:
    def __init__(self, log):
        self.log = log

    def __bool__(self):
        self.log.append(7)
        raise ValueError()

class Comparing:
    def __init__(self, log):
        self.log = log

    def __eq__(self, other):
        self.log.append(3)
        return Truth(self.log, 0)

    def __contains__(self, other):
        self.log.append(4)
        return Truth(self.log, 1)

class IndexValue:
    def __index__(self):
        return 2

class IndexedLength:
    def __len__(self):
        return IndexValue()

class BoolLength:
    def __len__(self):
        return True

# Implicit tests cannot dispatch to this source binding.
def bool(value):
    return False

def if_statement(n):
    log = []
    x = Truth(log, 0)
    if x:
        return 99
    return len(log)

def conditional(n):
    log = []
    x = Truth(log, n)
    result = 5 if x else 8
    return result * 10 + len(log)

def negate(n):
    log = []
    result = not Truth(log, 0)
    return (10 if result else 0) + len(log)

def and_value(n):
    log = []
    x = Truth(log, 0)
    result = x and Truth(log, n)
    return result.value * 10 + len(log)

def or_value(n):
    log = []
    x = Truth(log, 0)
    result = x or Truth(log, n)
    return result.value * 10 + len(log)

def and_short(n):
    log = []
    x = Truth(log, 0)
    result = x and (1 // 0)
    return result.value + len(log)

def or_short(n):
    log = []
    x = Truth(log, n)
    result = x or (1 // 0)
    return result.value * 10 + len(log)

def while_length(n):
    x = Countdown(n)
    total = 0
    while x:
        x.n -= 1
        total += 1
    return total * 10 + x.calls

def empty_containers(n):
    a = []
    b = {}
    c = ()
    if a or b or c:
        return 99
    a.append(n)
    if a:
        return 1
    return 98

def comparison_result(n):
    log = []
    x = Comparing(log)
    value = x != n
    return (100 if value else 0) + len(log) * 10 + log[0]

def membership_result(n):
    log = []
    x = Comparing(log)
    value = n not in x
    return (100 if value else 0) + len(log) * 10 + log[0]

def finalizer(n):
    log = []
    try:
        try:
            if Raising(log):
                return 99
        finally:
            log.append(8)
    except ValueError:
        return len(log) * 100 + log[0] * 10 + log[1]
    return 98

def boolean_length(n):
    return len(BoolLength())

def index_length(n):
    return len(IndexedLength())

def index_truth(n):
    return 3 if IndexedLength() else 4

def if_and(n):
    log = []
    x = Truth(log, 0)
    if x and Truth(log, n):
        return 99
    return len(log)

def if_or(n):
    log = []
    x = Truth(log, n)
    if x or Truth(log, 0):
        return len(log)
    return 99

def if_not_and(n):
    log = []
    x = Truth(log, 0)
    if not (x and Truth(log, n)):
        return len(log)
    return 99

def mixed_condition(n):
    log = []
    a = Truth(log, n)
    b = Truth(log, 0)
    c = Truth(log, 3)
    if (a or b) and c:
        return len(log) * 10 + log[1]
    return 99

def conditional_condition(n):
    log = []
    a = Truth(log, 0)
    b = Truth(log, n)
    if ((a and b) if n > 0 else b):
        return 99
    return len(log)

def value_not_and(n):
    log = []
    a = Truth(log, 0)
    result = not (a and Truth(log, n))
    return len(log) * 10 + (1 if result else 0)

def value_and_chain(n):
    log = []
    a = Truth(log, 0)
    result = a and Truth(log, n) and Truth(log, 3)
    return len(log) * 10 + result.value

def value_mixed_chain(n):
    log = []
    a = Truth(log, n)
    b = Truth(log, 0)
    c = Truth(log, 3)
    result = (a or b) and c
    return len(log) * 10 + result.value

def value_or_chain(n):
    log = []
    a = Truth(log, 0)
    b = Truth(log, 0)
    c = Truth(log, 3)
    result = (a or b) or c
    return len(log) * 10 + result.value

def later_truth_test(n):
    log = []
    a = Truth(log, 0)
    result = a and Truth(log, n) and Truth(log, 3)
    if result:
        return 99
    return len(log)

class Flip:
    def __init__(self, log):
        self.log = log
        self.value = False

    def __bool__(self):
        before = self.value
        self.value = not before
        self.log.append(1)
        return before

def changing_value_truth(n):
    log = []
    x = Flip(log)
    result = (x and Truth(log, n)) or Truth(log, 3)
    return len(log) * 10 + result.value

def changing_condition_truth(n):
    log = []
    x = Flip(log)
    if x and Truth(log, n):
        return 99
    return len(log)

def independent_truth(n):
    log = []
    x = Flip(log)
    result = x and Truth(log, n)
    if result:
        return len(log)
    return 99

def lifted_value(n):
    log = []
    x = Truth(log, 0)
    result = x and [v for v in (1, 2)]
    return len(log) * 10 + result.value

def lifted_condition(n):
    log = []
    x = Truth(log, 0)
    if x and [v for v in (1, 2)]:
        return 99
    return len(log)

def lifted_not(n):
    log = []
    x = Truth(log, 0)
    if not (x and [v for v in (1, 2)]):
        return len(log)
    return 99

def lifted_selected_condition(n):
    log = []
    x = Truth(log, n)
    if x and [v for v in (1, 2)]:
        return len(log)
    return 99

def lifted_generator(log):
    x = Truth(log, 0)
    if x and [v for v in (1, 2)]:
        yield 99
    else:
        yield len(log)

def generator_lifted_condition(n):
    log = []
    g = lifted_generator(log)
    return next(g)
