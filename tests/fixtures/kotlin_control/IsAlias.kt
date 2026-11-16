package k

import k.Mode as Setting

// A `when` entry's type is its text, resolved as Kotlin resolves the name: through the
// file's imports first, so `Setting` is the analysed enum `k.Mode`.
fun whenAlias(a: Any?): Int = when (a) {
    is Setting -> 1
    else -> 2
}

fun isAlias(a: Any?): Boolean = a is Setting
