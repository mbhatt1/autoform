"""Exception selection cases compared directly with CPython."""


def mismatched(a):
    try:
        raise TypeError()
    except ValueError:
        return a


def matched(a):
    try:
        raise ValueError()
    except ValueError:
        return a


def lookup_parent(a):
    try:
        raise KeyError()
    except LookupError:
        return a


def arithmetic_parent(a):
    try:
        return a // 0
    except ArithmeticError:
        return a


def ordered(a):
    try:
        if a < 0:
            raise ValueError()
        if a == 0:
            raise TypeError()
        raise KeyError()
    except ValueError:
        return a + 1
    except TypeError:
        return a + 2
    except LookupError:
        return a + 3


def first_match(a):
    try:
        raise KeyError()
    except Exception:
        return a + 1
    except LookupError:
        return a + 2


def tuple_handler(a):
    try:
        raise TypeError()
    except (
        ValueError,  # A multiline header cannot be recovered by line splitting.
        TypeError,
    ):
        return a


def exception_excludes_exit(a):
    try:
        raise SystemExit()
    except Exception:
        return a


def base_includes_exit(a):
    try:
        raise SystemExit()
    except BaseException:
        return a


def bare_includes_interrupt(a):
    try:
        raise KeyboardInterrupt()
    except:
        return a


def nested_outer(a):
    try:
        try:
            raise TypeError()
        except ValueError:
            return a + 1
    except TypeError:
        return a + 2


def handler_exception_escapes(a):
    try:
        raise ValueError()
    except ValueError:
        raise TypeError()
    except TypeError:
        return a


def else_exception_escapes(a):
    try:
        x = a
    except TypeError:
        return a
    else:
        raise TypeError()


def else_skipped(a):
    try:
        raise ValueError()
    except ValueError:
        x = a
    else:
        x = 99
    return x


def finally_overrides_unmatched(a):
    try:
        raise TypeError()
    except ValueError:
        return a + 1
    finally:
        return a + 2


def synthetic_name_collision(a):
    __exc = a
    __else_ok1 = a + 1
    try:
        raise ValueError()
    except ValueError:
        pass
    else:
        return 99
    return __exc + __else_ok1


def empty_tuple(a):
    try:
        raise ValueError()
    except ():
        return a


def unrelated_local_binding(a):
    # A binding in an unrelated function must not hide the builtin elsewhere.
    ValueError = a
    return ValueError


def dynamic_handler(a):
    kind = ValueError
    try:
        raise TypeError()
    except kind:
        return a


def shadowed_handler(ValueError):
    try:
        raise TypeError()
    except ValueError:
        return 99


def exception_binding(a):
    try:
        raise ValueError(a)
    except ValueError as error:
        return error.args[0]
