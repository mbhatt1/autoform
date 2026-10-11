"""A small module the pull-request demo changes (see docs/github-action.md)."""


def unit_price(total, count):
    if count == 0:
        return 0
    return total // count


def total_price(unit, count):
    return unit * count
