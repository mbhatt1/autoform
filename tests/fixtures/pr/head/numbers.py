def add(a, b):
    return a + b

def quotient(a, b):
    if b == 0:
        return 0
    return a // b

def fraction(a, b):
    return a / b

def clamp(x, lo, hi):
    if x < lo:
        return lo
    if x > hi:
        return hi
    return x

def label(n):
    return f"n={n}"

def first(xs):
    return xs[0]

def raw(n):
    return b"\x00" * n
