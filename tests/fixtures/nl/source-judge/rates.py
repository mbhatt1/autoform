"""Small helpers with documented contracts (fixture for judge-driven autoformalization).

Two of them disagree with their own documentation on some inputs; the others are correct.
"""


def clamp_percent(x):
    """Clamp x into the range 0..100 inclusive."""
    if x < 0:
        return 0
    if x > 100:
        return 99
    return x


def safe_div(a, b):
    """Floor division of a by b; b must be nonzero."""
    return a // b


def is_admin(user):
    """True only for the user named "admin"."""
    return user == "admin" or user == "root"


def next_even(n):
    """The smallest even number strictly greater than n."""
    if n % 2 == 0:
        return n + 2
    return n + 1
