def replacement(f):
    def inner():
        return 9
    return inner

@replacement
def decorated(a):
    return a

def call_decorated():
    return decorated()

class Outer:
    def f(self):
        return 0

def Outer(a):
    def inner(self):
        return self
    return inner(a)

class Private:
    def f(self, __value):
        return __value

def private_positional():
    return Private().f(11)

def private_keyword():
    return Private().f(_Private__value=13)

def private_unmangled():
    return Private().f(__value=17)

class Nested:
    def outer(self, a):
        def inner(self):
            return self
        return inner(a)

def nested_call():
    return Nested().outer(19)

class Collision:
    pass

def Collision(a):
    def inner(self):
        return self
    return inner(self=a)

def nested_extra(a):
    def inner(b):
        return b
    return inner(a, 99)


class LexicalPrivate:
    def outer(self):
        def local(__value):
            return __value
        return local(_LexicalPrivate__value=31)


def nested_private():
    return LexicalPrivate().outer()


def ordinary_private_name(__value):
    return __value


class Dunder:
    def method(self, __value__):
        return __value__


def dunder_keyword():
    return Dunder().method(__value__=37)


class ___:
    def method(self, __value):
        return __value


def underscore_class():
    return ___().method(__value=41)
