"""A tiny module whose functions read module-level state (translate-stage fixture)."""

LIMIT = 3
SCALE = {"small": 1, "large": 10}


def add(a, b):
    """Sum of two numbers."""
    return a + b


def over_limit(x):
    return x > LIMIT


def scaled(kind, n):
    return SCALE[kind] * n


def clamp(x):
    """Cap x at LIMIT."""
    if over_limit(x):
        return LIMIT
    return x


class Counter:
    def __init__(self, start):
        self.n = start

    def bump(self):
        self.n = add(self.n, 1)
        return self.n
