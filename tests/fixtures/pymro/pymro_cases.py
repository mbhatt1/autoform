"""Differential fixture for Python method resolution and name scoping (STRATEGY.md §62).

Every `case_*` function takes no arguments. `tests/test_pymro_cpython.py` runs each one under
CPython and compares the result with the value Core computes for the SAME source after the
whole pipeline -- `pysrc2cpg` -> `cartographer/export_ast.sc` -> `cartographer/render_lean.py`
-> `Autoform/PyMroProgram.lean` -- pinned by `#guard_msgs` in `Autoform/PyMro.lean`.

Two rules are under test, both of which Core used to get wrong by matching names on their
suffix (docs/conformance.md finding 3):

* a method is looked up along `type(obj).__mro__` (C3), so a subclass override wins over the
  base's own method even when the base is the one calling it, and `super()` continues along
  the MRO of the INSTANCE, not of the class it is written in;
* a bare name is a local, else a module global, else a builtin -- never "any function whose
  qualified name ends in that name".
"""

import collections.abc
from abc import ABC


# ---- overriding and inheritance -----------------------------------------------


class Store:
    def __init__(self):
        self.count = 0

    def lookup(self, key):
        if key == 1:
            return "one"
        return self.on_missing(key)

    def on_missing(self, key):
        raise KeyError(key)

    def size(self):
        self.count = self.count + 1
        return self.count


class DefaultStore(Store):
    def on_missing(self, key):
        return ("default", key)


def case_override_reached_from_base():
    # `Store.lookup` calls `self.on_missing`: CPython takes the subclass override. This is
    # the `__missing__` shape of cachetools' `DefaultCache` tests.
    s = DefaultStore()
    return s.lookup(7)


def case_base_method_unchanged():
    s = Store()
    try:
        return s.lookup(7)
    except KeyError:
        return "KeyError"


def case_inherited_method():
    s = DefaultStore()
    s.size()
    return s.size()


def case_inherited_init():
    s = DefaultStore()
    return s.count


def case_base_method_through_class_value():
    # An inherited method reached through the subclass's class value.
    s = DefaultStore()
    return DefaultStore.size(s)


# ---- C3 and super() ---------------------------------------------------------------


class Root:
    def who(self):
        return ["Root"]

    def tag(self):
        return "root"


class Left(Root):
    def who(self):
        rest = super().who()
        return ["Left"] + rest


class Right(Root):
    def who(self):
        rest = super().who()
        return ["Right"] + rest

    def tag(self):
        return "right"


class Bottom(Left, Right):
    def who(self):
        rest = super().who()
        return ["Bottom"] + rest


def case_diamond_mro_lookup():
    # Bottom -> Left -> Right -> Root: `tag` is found in Right, not in Root, although Left
    # (the first base) inherits Root's.
    return Bottom().tag()


def case_super_follows_instance_mro():
    # Left's `super()` is Right for a Bottom, Root for a plain Left.
    return Bottom().who()


def case_super_single():
    return Left().who()


class Counter:
    def __init__(self, start):
        self.n = start


class StepCounter(Counter):
    def __init__(self, start, step):
        super().__init__(start)
        self.step = step

    def bump(self):
        self.n = self.n + self.step
        return self.n


def case_super_init_with_args():
    c = StepCounter(10, 3)
    c.bump()
    return c.bump()


# ---- what the class table cannot answer -------------------------------------------


class Shelf:
    def get(self, k):
        return ("get", k)

    fetch = get

    @staticmethod
    def make(k):
        return ("make", k)


def case_staticmethod_through_instance():
    return Shelf().make(5)


def case_class_attribute_alias():
    # `fetch = get` is a class attribute Core does not model: a hole, not a guess.
    return Shelf().fetch(5)


class Bag(collections.abc.Mapping):
    def __init__(self):
        self.v = 1

    def __getitem__(self, k):
        if k == "a":
            return self.v
        raise KeyError(k)

    def __len__(self):
        return 1

    def __iter__(self):
        return iter(["a"])


def case_external_base_method():
    # `Mapping.get` is defined outside the corpus: a hole at the external base.
    return Bag().get("a")


def case_own_method_before_external_base():
    return Bag().__getitem__("a")


def case_absent_method():
    # CPython raises AttributeError; Core has no `object` attributes to consult.
    try:
        return Store().nonexistent()
    except AttributeError:
        return "AttributeError"


def make_base():
    return Store


class Dynamic(make_base()):
    def extra(self):
        return 1


def case_unresolvable_base():
    # The base is a call: the exporter cannot know the class, so it is left out of the
    # table, and every lookup on it is a hole.
    return Dynamic().size()


# ---- bare names ---------------------------------------------------------------------


class Holder:
    def orphan_fn(self):
        return "method"

    def scale(self, x):
        return x * 100


def case_unbound_name_is_not_a_method():
    # `orphan_fn` exists only as a METHOD. As a bare name it is unbound: CPython raises
    # NameError. Suffix resolution used to call the method.
    try:
        return orphan_fn()  # noqa: F821
    except NameError:
        return "NameError"


def case_local_function_value_shadows_method():
    scale = lambda x: x + 1  # noqa: E731
    return scale(4)


def case_parameter_function_value():
    return apply_it(len, [1, 2, 3])


def apply_it(fn, arg):
    return fn(arg)


MODULE_LIMIT = 9


def case_module_global_read():
    return MODULE_LIMIT + 1


def case_builtin_call():
    return len("abcd")


# ---- additions after the merge with boxed containers ------------------------------


class Shape(ABC):
    def area(self):
        return 0

    def describe(self):
        return ("shape", self.area())


class Square(Shape):
    def __init__(self, s):
        self.s = s

    def area(self):
        return self.s * self.s


def case_abc_base_is_transparent():
    # `abc.ABC` defines nothing an instance lookup can find, so it does not block the walk.
    return Square(3).describe()


class Callbacks:
    def handler(self):
        return "method"


def case_instance_attribute_shadows_method():
    # The instance's own attribute wins over the class's method in CPython. Core does not
    # call it (a hole), but it must not call the method instead.
    c = Callbacks()
    c.handler = lambda: "instance"
    return c.handler()


class Grid:
    def __init__(self):
        self.total = 0

    def __setitem__(self, k, v):
        self.total = self.total + v


class SubGrid(Grid):
    pass


def case_inherited_setitem():
    # `g[k] = v` dispatches `__setitem__` along the MRO: SubGrid inherits Grid's.
    g = SubGrid()
    g[1] = 5
    g[2] = 7
    return g.total


# Builtin exception classes resolve through `builtins` whatever the module globals hold,
# and `raise C` with `C` a class raises `C()`. Core models the classes in
# `Stdlib.excNames`; its payload for an instance is the class name.


def case_raise_builtin_exception_class():
    # The cachetools `_TimedCache.expire` idiom.
    raise NotImplementedError


def case_raise_builtin_exception_class_from_local():
    # The class as a VALUE, held in a local, then raised: still instantiated.
    err = KeyError
    raise err


def case_raise_builtin_exception_instance():
    # The explicit call, for contrast: the same payload as raising the class.
    raise TypeError("bad")


def case_local_shadows_builtin_exception_name():
    # A local binding wins over `builtins`.
    ValueError = "mine"  # noqa: N806
    return ValueError


def case_raise_unmodelled_builtin_exception_class():
    # `DeprecationWarning` is a builtin Core has no model of: still a hole, not a guess.
    raise DeprecationWarning
