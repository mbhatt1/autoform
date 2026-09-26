"""Typed boundary inputs shared by the runtime oracle and the machine regression search."""


def typed_boundary_pool(ctype):
    """Width and signedness boundaries of one ABI integer type, as Python ints.

    `randint(-20, 20)` can never make a 64-bit multiply overflow, so an oracle drawing
    only from it reports "agrees" for `lcm(a, b) = a * b / gcd(a, b)` on every input it
    tries and never meets the case the kernel fixed in 74a5fef7cb08. These are the
    values where widths matter: powers of two straddling 32 and 64 bits, the type's
    extremes, and their neighbours.
    """
    import ctypes
    bits = ctypes.sizeof(ctype) * 8
    signed = ctype(-1).value < 0
    return integer_boundary_pool(bits, signed)


def integer_boundary_pool(bits, signed):
    """The same pool, for a width and signedness given directly."""
    magnitudes = [1, 2, 3, 7, 8, 63, 64, 255, 256, 65535, 65536]
    for k in (31, 32, 40, 48, 62, 63):
        magnitudes += [(1 << k) - 1, 1 << k, (1 << k) + 1]
    if signed:
        top = (1 << (bits - 1)) - 1
        pool = [v for v in magnitudes if v <= top] + [top, top - 1]
        pool += [-v for v in pool] + [-top - 1, -top]
    else:
        top = (1 << bits) - 1
        pool = [v for v in magnitudes if v <= top] + [top, top - 1]
    return sorted(set(pool))
