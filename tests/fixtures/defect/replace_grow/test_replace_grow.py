"""Witness for docs/evidence-cachetools.md: replacing an existing key with a larger value.

These are cachetools 7.1.7's `CacheTestMixin.test_getsizeof_replace_*` regression tests
(tests/__init__.py of the 7.1.7 sdist), transcribed with `getsizeof=len` over string
values instead of `lambda x: x` over integers. The builtin `len` is what cachetools'
own manual uses (docs/index.rst, the `@cached` example); the lambda lives in the test
module, so the oracle refuses a receiver holding it unless the lambda is indexed.

Run against cachetools 7.1.6 this suite fails in `test_getsizeof_replace_grow`
(len 1 where 2 is expected) -- the defect fixed by 7.1.7 (CHANGELOG: "Improve
Cache.__setitem__ behavior when replacing an existing cache item with a larger value").
Run against 7.1.7 it passes.
"""
import unittest

from cachetools import Cache


class ReplaceTest(unittest.TestCase):
    def test_getsizeof_replace_grow(self):
        cache = Cache(maxsize=10, getsizeof=len)

        cache["a"] = "xxx"
        cache["b"] = "xxxx"
        self.assertEqual(2, len(cache))
        self.assertEqual(7, cache.currsize)

        # growing an existing entry must only reserve the additional size
        cache["b"] = "xxxxxxx"
        self.assertEqual(2, len(cache))
        self.assertEqual(10, cache.currsize)
        self.assertEqual("xxx", cache["a"])
        self.assertEqual("xxxxxxx", cache["b"])

    def test_getsizeof_replace_same_size(self):
        cache = Cache(maxsize=10, getsizeof=len)

        cache["a"] = "xxx"
        cache["b"] = "xxxx"
        self.assertEqual(7, cache.currsize)

        cache["b"] = "yyyy"
        self.assertEqual(2, len(cache))
        self.assertEqual(7, cache.currsize)
        self.assertEqual("xxx", cache["a"])
        self.assertEqual("yyyy", cache["b"])

    def test_getsizeof_replace_shrink(self):
        cache = Cache(maxsize=10, getsizeof=len)

        cache["a"] = "xxx"
        cache["b"] = "xxxx"
        self.assertEqual(7, cache.currsize)

        cache["b"] = "y"
        self.assertEqual(2, len(cache))
        self.assertEqual(4, cache.currsize)
        self.assertEqual("xxx", cache["a"])
        self.assertEqual("y", cache["b"])
