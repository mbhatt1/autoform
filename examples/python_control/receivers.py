"""Receiver shapes that require explicit unsupported binding outcomes."""


class Receiver:
    def absent():
        return 1

    def keyword(*, self):
        return 2

    def renamed(receiver, a):
        return a

    def star_self(*self):
        return len(self)

    @staticmethod
    def static(self, a):
        return (self, a)

    @classmethod
    def class_named(cls, a):
        return a

    @classmethod
    def class_self(self, a):
        return a

    def collect(self, **kw):
        return 1

    def positional_collect(self, /, **kw):
        return 2
