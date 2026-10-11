from pricing import total_price, unit_price


def test_unit_price():
    assert unit_price(10, 2) == 5
    assert unit_price(7, 2) == 3
    assert unit_price(5, 0) == 0


def test_total_price():
    assert total_price(3, 4) == 12
