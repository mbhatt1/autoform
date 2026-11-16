package k

fun subj(x: Int): Int = when (x) {
    1 -> 10
    2, 3 -> 20
    in 5..9 -> 30
    !in 0..100 -> 40
    in 10 until 20 -> 50
    else -> -1
}

fun strWhen(s: String?): Int = when (s) {
    null -> 0
    "a" -> 1
    "b", "c:d" -> 2
    else -> 3
}

fun longWhen(x: Long): String = when (x) {
    1L -> "one"
    -2L -> "minus two"
    else -> "other"
}

fun charWhen(c: Char): Int = when (c) {
    'a' -> 1
    in 'b'..'y' -> 2
    else -> 3
}

fun boolWhen(b: Boolean): Int = when (b) {
    true -> 1
    false -> 0
}

fun blockWhen(x: Int): Int = when (val y = x * 2) {
    2 -> {
        val z = y + 1
        z * 3
    }
    4 -> y - 100
    else -> y
}

fun firstMatch(x: Int): Int = when (x) {
    in 0..10 -> 1
    5 -> 2
    else -> 3
}

fun lazyWhen(x: Int, d: Int): Int = when (x) {
    1 -> 1
    10 / d -> 2
    else -> 3
}

fun stmtWhen(x: Int): Int {
    var r = 0
    when (x) {
        1 -> r = 5
        2, 3 -> {
            r = 6
            r += 1
        }
        in 10..20 -> r = 7
        else -> r = -1
    }
    return r
}

fun stmtWhenNoElse(s: String): Int {
    var r = 9
    when (s) {
        "x" -> r = 1
        "y" -> r = 2
    }
    return r
}

fun stmtNullable(x: Int?): Int {
    var r = 0
    when (x) {
        1 -> r = 1
        null -> r = 2
        in 5..6, -> r = 3
    }
    return r
}

fun noSubj(x: Int): Int {
    var r = 0
    when {
        x < 0 -> r = -1
        x > 10 -> r = 1
    }
    return r
}

fun elvis(s: String?): String = s ?: "none"

fun elvisChain(a: String?, b: String?): String = a ?: b ?: "z"

fun elvisReturn(x: Int?): Int {
    val t: Int = x ?: return -1
    return t * 2
}

fun nullableLong(x: Long?): Int = when (x) {
    1L -> 1
    -2L -> 2
    in 10L..20L -> 3
    null -> 4
    else -> 5
}

fun elvisThrow(s: String?): String {
    val t = s ?: throw IllegalArgumentException("missing")
    return t
}

fun ifThrow(x: Int): Int = if (x > 0) x else throw IllegalStateException("negative")

enum class Color { RED, GREEN }

fun enumWhen(c: Color): Int = when (c) {
    Color.RED -> 1
    Color.GREEN -> 2
}

fun isWhen(a: Any?): Int = when (a) {
    is String -> 1
    else -> 2
}

fun mixedWhen(a: Any?): Int = when (a) {
    1, is String -> 1
    else -> 2
}

fun tryWhen(x: Int): Int = try {
    10 / x
} catch (e: ArithmeticException) {
    -1
}

// Enum entries: `E.X` is the model's `fnref "<E>$<X>"`, in every position.
fun enumOf(i: Int): Color = if (i > 0) Color.RED else Color.GREEN

fun enumIs(c: Color?): Boolean = c == Color.GREEN

fun enumStmt(c: Color): Int {
    var r = 0
    when (c) {
        Color.RED -> r = 5
        Color.GREEN -> r = 6
    }
    return r
}

enum class Level(val weight: Int) {
    LOW(1), HIGH(9);

    fun next(): Level = when (this) {
        LOW -> HIGH
        HIGH -> LOW
    }
}

fun levelWhen(l: Level?): Int = when (l) {
    Level.LOW -> 1
    Level.HIGH -> 2
    null -> 0
}

// `?.` outside `?:`, String and collection properties, standard-library extensions.
fun safeLen(s: String?): Int? = s?.length

fun safeLenOr(s: String?): Int = s?.length ?: -1

fun pick(s: String?): String? = if (s == null || s.length > 3) null else s

fun safeCallOnCall(s: String?): Int = pick(s)?.length ?: -7

fun safeChain(s: String?): Int = pick(s)?.toString()?.length ?: -8

fun strProps(s: String): Int = s.length * 10 + (if (s.isEmpty()) 1 else 0) + (if (s.isNotEmpty()) 2 else 0)

fun isTest(a: Any?): Boolean = a is String

fun <T> runIt(f: () -> T): T = f()

// A `?.` only inside the lambda argument belongs to the lambda, not to `runIt(..)`.
fun nestedSafe(s: String?): Int? = runIt { s?.length }

class Holder(val v: String?) {
    // `v?.length` has the receiver `this.v`, whose code is not a prefix of the node's.
    fun len(): Int? = v?.length
}
