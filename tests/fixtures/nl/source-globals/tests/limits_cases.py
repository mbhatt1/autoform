# Named so pytest does not collect it: it is source for the translate stage's test index.
from limits import clamp, Counter


def test_clamp():
    assert clamp(5) == 3
    assert clamp(2) == 2


def test_counter():
    c = Counter(1)
    assert c.bump() == 2
