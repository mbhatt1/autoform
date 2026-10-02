"""Differential cases for boxed Python containers (docs/boxed-containers.md).

Every function here takes no arguments and returns an int or a bool, or raises. The
exporter's output for this file is committed beside it as `ast-BoxedSample.json`;
`tests/test_boxed_containers.py` runs each function under CPython and under the Lean
interpreter and compares. Regenerate the AST with the command in that test's docstring.
"""


def alias():
    b = [0, 5]
    a = b
    b[0] = 1
    return a[0]


def neg():
    xs = [1, 2, 3]
    xs[-1] = 9
    return xs[-1] + xs[0]


def neg_read():
    return (7, 8, 9)[-1]


def oob():
    xs = [1]
    xs[3] = 2
    return 0


def oob_neg():
    xs = [1]
    xs[-2] = 2
    return 0


def oob_read():
    xs = [1]
    return xs[1]


def dset():
    d = {}
    d['k'] = 1
    e = d
    e['j'] = 2
    return d['j'] * 10 + d['k']


def dlit():
    d = {'a': 1, 'b': 2}
    return d['b']


def kerr():
    d = {}
    return d['missing']


def app():
    a = []
    b = a
    b.append(1)
    b.append(2)
    x = a.pop()
    return len(a) * 10 + x


def pop_tmp():
    d = {'k': 1}
    t = d
    t.pop('k')
    return len(d)


def ext():
    a = [1]
    b = a
    b.extend([2, 3])
    b.insert(0, 0)
    return a[0] * 100 + len(a)


def setdef():
    d = {}
    d.setdefault('k', []).append(1)
    return len(d['k'])


def nested():
    a = [[0]]
    b = a[0]
    b.append(1)
    return len(a[0])


def mut(xs):
    xs.append(9)


def call_mut():
    a = []
    mut(a)
    return len(a)


def comp_len():
    ys = [y * 2 for y in [1, 2, 3]]
    return len(ys)


def comp_sum():
    ys = [y * 2 for y in [1, 2, 3]]
    return sum(ys)


def delk():
    d = {'a': 1}
    del d['a']
    return len(d)


def del_pos():
    xs = [1, 2]
    del xs[0]
    return xs[0]


def del_missing():
    d = {}
    del d['zz']
    return 0


def truth():
    a = []
    if a:
        return 1
    return 2


def not_empty():
    return not []


def tup():
    t = (1, 2)
    t[0] = 3
    return 0


def unhash():
    d = {}
    d[[1]] = 2
    return 0


def eq():
    return [1] == [1]


def is_():
    return [1] is [1]


def in_():
    return [1] in [[1]]


def order():
    d = {}
    d['b'] = 1
    d['a'] = 2
    d['b'] = 3
    return list(d) == ['b', 'a']


def dict_eq():
    d = {}
    d['b'] = 3
    d['a'] = 2
    e = {}
    e['a'] = 2
    e['b'] = 3
    return d == e


def copy_fresh():
    a = [1]
    b = list(a)
    b.append(2)
    return len(a)


def iter_sum():
    t = 0
    for x in [1, 2, 3]:
        t = t + x
    return t


# The three below are NOT modelled and must come back as holes, never as answers.

def mutate_iter():
    xs = [1]
    n = 0
    for x in xs:
        n = n + 1
        if x == 1:
            xs.append(2)
    return n


def keys_view():
    d = {'a': 1}
    return len(d.keys())


def slc():
    xs = [1, 2, 3]
    xs[0:1] = [5]
    return xs[0]
