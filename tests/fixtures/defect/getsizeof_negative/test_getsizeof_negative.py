"""Witness for docs/evidence-cachetools-negative-size.md: a negative `getsizeof` value.

This is cachetools 7.1.5's `CacheTestMixin.test_getsizeof_negative` (tests/__init__.py of
the 7.1.5 sdist), unchanged except that the size function is a `def` instead of a lambda.
7.1.5's changelog: "Reject negative cache item ``getsizeof`` values." Run against 7.1.4
this fails (no `ValueError`); against 7.1.5 it passes.
"""
import unittest

from cachetools import Cache


def minus_one(_value):
    return -1


class NegativeSizeTest(unittest.TestCase):
    def test_getsizeof_negative(self):
        cache = Cache(maxsize=3, getsizeof=minus_one)

        with self.assertRaises(ValueError):
            cache[1] = 1

        self.assertEqual(0, len(cache))
        self.assertEqual(0, cache.currsize)
