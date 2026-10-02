"""Differential fixture for Python `/`, `//` and `bool`-is-an-`int` (STRATEGY.md item Q).

Every `case_*` function takes no arguments. `tests/test_pyarith_cpython.py` runs each one
under CPython and compares the result with the value Core computes for the SAME source
after the whole pipeline -- `pysrc2cpg` -> `cartographer/export_ast.sc` ->
`cartographer/render_lean.py` -> `Autoform/PyArithProgram.lean` -- pinned by
`#guard_msgs` in `Autoform/PyArith.lean`.

Operands are bound to locals first (`a = 7`) so that no frontend constant-folds the
operator away, and so the operator under test is the one the exporter emits.
"""

# ---- `/` is true division and returns a float ----------------------------------


def case_div_7_2():
    a = 7
    b = 2
    return a / b


def case_div_neg7_2():
    a = -7
    b = 2
    return a / b


def case_div_7_neg2():
    a = 7
    b = -2
    return a / b


def case_div_exact_is_float():
    a = 6
    b = 3
    return a / b


def case_div_zero():
    a = 1
    b = 0
    return a / b


def case_div_zero_numerator_negative_divisor():
    a = 0
    b = -3
    return a / b


def case_div_one_third():
    a = 1
    b = 3
    return a / b


def case_div_exactly_2pow53():
    # |operands| <= 2^53: both are exact binary64s, so one IEEE division is CPython's answer.
    a = 9007199254740992
    b = 2
    return a / b


def case_div_beyond_2pow53():
    # 2**53 + 1 is not a binary64. CPython rounds the QUOTIENT once; converting first and
    # dividing would round twice. Core refuses rather than guess.
    a = 9007199254740993
    b = 2
    return a / b


def case_div_big_int():
    a = 1000000000000000000000000000000
    b = 7
    return a / b


def case_div_big_divisor():
    a = 1
    b = 9007199254740993
    return a / b


def case_div_int_float():
    a = 7
    b = 2.0
    return a / b


def case_div_float_float():
    a = 7.5
    b = 2.5
    return a / b


# ---- `//` floors ---------------------------------------------------------------


def case_floordiv_7_2():
    a = 7
    b = 2
    return a // b


def case_floordiv_neg7_2():
    a = -7
    b = 2
    return a // b


def case_floordiv_7_neg2():
    a = 7
    b = -2
    return a // b


def case_floordiv_zero():
    a = 1
    b = 0
    return a // b


def case_mod_neg7_3():
    a = -7
    b = 3
    return a % b


def case_div_and_floordiv_together():
    a = 7
    b = 2
    return (a / b, a // b, a % b)


# ---- bool is an int ------------------------------------------------------------


def case_bool_eq_int():
    t = True
    one = 1
    return (t == one, one == t, t != one)


def case_bool_ne_int():
    t = True
    two = 2
    return (t == two, t != two)


def case_false_eq_zero():
    f = False
    zero = 0
    return (f == zero, zero == f)


def case_bool_eq_float():
    t = True
    x = 1.0
    return (t == x, x == t)


def case_bool_add_int():
    t = True
    one = 1
    return (t + one, one + t)


def case_bool_add_bool():
    t = True
    return t + t


def case_bool_sub():
    t = True
    f = False
    return (f - t, 2 - t, t - 1)


def case_bool_mul():
    t = True
    f = False
    five = 5
    return (t * five, five * f)


def case_bool_neg():
    t = True
    return -t


def case_bool_invert():
    t = True
    f = False
    return (~t, ~f)


def case_bool_lt():
    t = True
    two = 2
    return (t < two, two > t, t <= 1, t >= 2)


def case_bool_div():
    t = True
    two = 2
    return (t / two, two / t)


def case_bool_div_zero():
    t = True
    f = False
    return t / f


def case_bool_floordiv_mod():
    t = True
    two = 2
    return (t // two, two // t, t % two, two % t)


def case_bool_shift():
    t = True
    three = 3
    return (t << three, three >> t)


def case_bool_and_stays_bool():
    t = True
    f = False
    return (t & t, t & f, f & f)


def case_bool_or_stays_bool():
    t = True
    f = False
    return (t | t, t | f, f | f)


def case_bool_xor_stays_bool():
    t = True
    f = False
    return (t ^ t, t ^ f, f ^ f)


def case_bool_bitwise_with_int():
    # `bool & int` is an int, not a bool.
    t = True
    three = 3
    return (t & three, three | t, t ^ three)


def case_bool_plus_float():
    t = True
    x = 1.5
    return (t + x, x * t)


def case_not_bool():
    t = True
    return (not t, not 0)


def case_bool_dict_key_lookup():
    d = {1: 'a', 0: 'b'}
    t = True
    f = False
    return (d[t], d[f])


def case_int_dict_key_lookup_by_bool_key():
    d = {True: 'x'}
    one = 1
    return d[one]


def case_bool_in_list():
    xs = [1, 2]
    t = True
    return (t in xs, 1 in [t], 2 in [t], False in [0])


def case_bool_tuple_eq():
    t = True
    return ((t, 2) == (1, 2), (1, 2) == (t, 3))


def case_bool_list_eq():
    t = True
    return [t, 0] == [1, False]
