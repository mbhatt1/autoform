"""Differential fixture for Python calling convention and scoping (STRATEGY.md §58).

Every `case_*` function takes no arguments. `tests/test_pyscoping_cpython.py` runs each one
under CPython and compares the result with the value Core computes for the SAME source
after the whole pipeline -- `pysrc2cpg` -> `cartographer/export_ast.sc` ->
`cartographer/render_lean.py` -> `Autoform/PyScopingProgram.lean` -- pinned by
`#guard_msgs` in `Autoform/PyScoping.lean`.

Names are deliberately distinctive: `Expr.call` resolves a bare name against the whole
function table by suffix before it looks at local variables, so a local called `f` could
reach an unrelated function `...x.f`. That is a separate, recorded Core rule; this fixture
does not try to test it.
"""

# ---- default parameter values -------------------------------------------------


def dflt_lits(a, b=10, c=None, d="s", e=True, f=(), g=-3, h=0.5):
    return (a, b, c, d, e, f, g, h)


def case_default_all():
    return dflt_lits(1)


def case_default_some():
    return dflt_lits(1, 2, d="t")


def case_default_by_keyword():
    return dflt_lits(a=5, g=7)


def dflt_mutable(x, acc=[]):
    return acc + [x]


def case_mutable_default_supplied():
    return dflt_mutable(1, [0])


def case_mutable_default_needed():
    # CPython evaluates `[]` once, at `def` time; Core does not run the `def`, so a call
    # that needs this default is a hole (`param:default-nonliteral`), never a fresh `[]`.
    return dflt_mutable(1)


GLOBAL_LIMIT = 4


def dflt_global(x, lim=GLOBAL_LIMIT):
    return (x, lim)


def case_global_default_supplied():
    return dflt_global(1, 2)


def case_global_default_needed():
    return dflt_global(1)


def case_lambda_default():
    adder_fn = lambda x, y=2: x + y
    return adder_fn(1)


class Shelf:
    def get(self, key, default=None, *, strict=False):
        return (key, default, strict)


def case_method_default():
    shelf_obj = Shelf()
    return shelf_obj.get(1)


def case_method_default_kwonly():
    shelf_obj = Shelf()
    return shelf_obj.get(1, 2, strict=True)


def _underscored(_k, _v=1):
    # Leading underscores: the signature reader once refused these (Java's
    # `isUnicodeIdentifierStart('_')` is false) and holed the whole function.
    return (_k, _v)


def case_underscored_default():
    return _underscored(0)


# ---- keyword-only and positional-only parameters --------------------------------


def kwo(a, *, b, c=3):
    return (a, b, c)


def case_kwonly():
    return kwo(1, b=2)


def case_kwonly_positional_rejected():
    return kwo(1, 2)


def kw_after_star(*args, key=None, **kw):
    return (args, key, kw)


def case_kw_after_varargs():
    return kw_after_star(1, 2)


def case_kw_after_varargs_named():
    return kw_after_star(1, key=5, z=6)


def posonly(a, b=2, /, c=3):
    return (a, b, c)


def case_posonly():
    return posonly(1)


def case_posonly_keyword_rejected():
    return posonly(1, b=5)


def posonly_kw(a, /, **kw):
    return (a, kw)


def case_posonly_name_goes_to_kwargs():
    return posonly_kw(1, a=2)


# ---- nonlocal ---------------------------------------------------------------


def make_counter():
    n = 0

    def inc():
        nonlocal n
        n += 1
        return n

    inc()
    inc()
    return (n, inc())


def case_nonlocal_counter():
    return make_counter()


def make_pair(start):
    def bump_by(k):
        nonlocal start
        start = start + k
        return start

    def peek_at():
        return start

    return (bump_by, peek_at)


def case_nonlocal_shared_between_closures():
    fns = make_pair(10)
    bumper = fns[0]
    peeker = fns[1]
    bumper(5)
    bumper(1)
    return peeker()


def nonlocal_chain():
    x = 1

    def mid():
        def inner():
            nonlocal x
            x = x * 10

        inner()
        return x

    r = mid()
    return (r, x)


def case_nonlocal_through_two_levels():
    return nonlocal_chain()


def loop_total(xs):
    total = 0

    def add_one(v):
        nonlocal total
        total += v

    for v in xs:
        add_one(v)
    return total


def case_nonlocal_in_a_loop():
    return loop_total([1, 2, 3])


# ---- starred assignment ---------------------------------------------------------


def star_tail(xs):
    a, *b = xs
    return (a, b)


def star_mid(xs):
    p, *q, r = xs
    return (p, q, r)


def star_head(xs):
    *c, d = xs
    return (c, d)


def case_star_tail_of_tuple_is_a_list():
    return star_tail((1, 2, 3))


def case_star_tail_empty():
    return star_tail([1])


def case_star_middle_of_str():
    return star_mid("abcd")


def case_star_too_short():
    return star_mid([1])


def case_star_head_of_str():
    return star_head("xyz")


def case_star_noniterable():
    return star_tail(5)
