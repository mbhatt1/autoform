"""Raise normalization and exception-constructor boundaries checked with CPython."""


def invalid_string(a):
    try:
        raise "ValueError"
    except ValueError:
        return a
    except TypeError:
        return a + 1


def invalid_number(a):
    try:
        raise 13
    except TypeError:
        return a


def invalid_none(a):
    try:
        raise None
    except TypeError:
        return a


def invalid_list(a):
    try:
        raise [a]
    except TypeError:
        return a


def invalid_dict(a):
    try:
        raise {"message": a}
    except TypeError:
        return a


def invalid_tuple(a):
    try:
        raise (a,)
    except TypeError:
        return a


def evaluation_before_validation(a):
    try:
        raise [a // 0]
    except ZeroDivisionError:
        return a
    except TypeError:
        return a + 1


def bare_class(a):
    try:
        raise ValueError
    except ValueError:
        return a


def bare_child_class(a):
    try:
        raise IndentationError
    except SyntaxError:
        return a


def class_alias(a):
    exception_type = ValueError
    try:
        raise exception_type
    except ValueError:
        return a


def shadowed_class(a):
    ValueError = a
    try:
        raise ValueError
    except TypeError:
        return a


def lambda_class_shadow(a):
    mapper = lambda ValueError: ValueError
    try:
        raise mapper(a)
    except TypeError:
        return a
    except ValueError:
        return a + 1


def invalid_syntax_details(a):
    try:
        raise SyntaxError("bad", a)
    except SyntaxError:
        return a
    except TypeError:
        return a + 1


def valid_syntax_details(a):
    try:
        raise SyntaxError("bad", ("file", 1, a, "text"))
    except SyntaxError:
        return a


def syntax_three_args(a):
    try:
        raise SyntaxError("bad", a, None)
    except SyntaxError:
        return a


def syntax_constructor_without_raise(a):
    try:
        value = SyntaxError("bad", a)
    except TypeError:
        return a
    return 99


def constructor_argument_error(a):
    try:
        raise ValueError(a // 0)
    except ZeroDivisionError:
        return a
    except ValueError:
        return a + 1


def dynamic_number(a):
    try:
        raise a
    except TypeError:
        return a


def implicit_typeerror_ignores_shadow(TypeError):
    try:
        raise "ValueError"
    except Exception:
        return TypeError


def ambiguous_exception_value(a):
    value = ValueError(a)
    raise value


def explicit_cause(a):
    raise ValueError(a) from TypeError()
