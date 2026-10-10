"""Local state must survive exception handlers and finalizers."""


def caught_raise(a):
    x = 0
    try:
        x = a
        raise ValueError()
    except ValueError:
        return x


def caught_expression(a):
    x = 0
    try:
        x = a
        y = 1 // 0
    except ZeroDivisionError:
        return x


def final_return(a):
    x = 0
    try:
        x = a
        return 11
    finally:
        return x


def final_pending_return(a):
    x = 0
    try:
        x = a
        return x
    finally:
        x = x + 1


def final_break(a):
    x = 0
    while True:
        try:
            x = a
            break
        finally:
            x = x + 1
    return x


def final_continue(a):
    x = 0
    i = 0
    while i < 2:
        try:
            i = i + 1
            continue
        finally:
            x = x + a
    return x


def final_exception(a):
    x = 0
    try:
        try:
            x = a
            raise ValueError()
        finally:
            x = x + 1
    except ValueError:
        return x


def final_nested_return(a):
    x = 0
    try:
        try:
            x = a
            return 11
        finally:
            x = x + 1
    finally:
        return x


def callee_raise(a):
    x = 999
    raise ValueError()


def caller_environment(a):
    x = 0
    try:
        x = a
        callee_raise(a)
    except ValueError:
        return x


def final_replaces_exception(a):
    x = 0
    try:
        x = a
        raise ValueError()
    finally:
        return x


def final_raises(a):
    x = 0
    try:
        try:
            x = a
            return 11
        finally:
            x = x + 1
            raise ValueError()
    except ValueError:
        return x
