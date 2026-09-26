# Named so pytest does not collect it: it is source for the translate stage's test index.
from rates import clamp_percent, safe_div, is_admin, next_even


def test_clamp_percent():
    assert clamp_percent(50) == 50
    assert clamp_percent(-3) == 0


def test_safe_div():
    assert safe_div(7, 2) == 3
    assert safe_div(9, 3) == 3


def test_is_admin():
    assert is_admin("admin")
    assert not is_admin("guest")


def test_next_even():
    assert next_even(3) == 4
    assert next_even(4) == 6
