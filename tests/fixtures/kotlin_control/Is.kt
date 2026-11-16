package k

// `is T` type tests: the exporter reads the type from the call's TYP_REF (a plain
// expression) or the entry's text (a `when`) and lowers the tests Core can decide.
class Widget(val n: Int)

enum class Mode { ON, OFF }

// The subject's static type already is the target: the test is a null check.
fun isSelf(a: String?): Boolean = a is String

fun isSelfQ(a: String?): Boolean = a is String?

fun isSelfClass(a: Widget?): Boolean = a is Widget

// `Any` is every non-null value; `Any?` also admits null.
fun isAny(a: Any?): Boolean = a is Any

fun isAnyQ(a: Any?): Boolean = a is Any?

fun isObject(a: Any?): Boolean = a is Object

// An analysed enum is final, so its values are exactly its entries.
fun isEnum(a: Any?): Boolean = a is Mode

fun notEnum(a: Any?): Boolean = a !is Mode

fun ifEnum(a: Any?): Int = if (a is Mode) 1 else 2

fun whenEnum(a: Any?): Int = when (a) {
    is Mode -> 1
    else -> 2
}

fun whenSelf(s: String?): Int = when (s) {
    is String -> 1
    else -> 2
}

fun whenAny(a: Any?): Int = when (a) {
    is Any -> 5
    else -> 7
}

fun whenNotEnum(a: Any?): Int = when (a) {
    !is Mode -> 1
    is Mode -> 2
    else -> 3
}

fun stmtWhenEnum(a: Any?): Int {
    var r = 0
    when (a) {
        is Mode -> r = 1
        else -> r = 2
    }
    return r
}

// `!!` before `is` is not `!is`: the operator is read between the subject and the type.
fun bangIs(a: Mode?): Boolean = a!! is Mode

// Core has no test for these types; they stay named holes (`op:is-type-test`).
fun plainIs(a: Any?): Boolean = a is String

fun plainIsNot(a: Any?): Boolean = a !is String

fun isInt(a: Any?): Boolean = a is Int

fun isLong(a: Any?): Boolean = a is Long

fun isBool(a: Any?): Boolean = a is Boolean

fun isClass(a: Any?): Boolean = a is Widget

fun ifString(a: Any?): Int = if (a is String) 1 else 2

fun whenString(a: Any?): Int = when (a) {
    is String -> 1
    else -> 2
}

// And these have no type here to read at all (`op:is:unknown-type`): a platform type,
// and a type parameter erased to `Object`.
fun isDate(a: Any?): Boolean = a is java.util.Date

inline fun <reified T> genericIs(x: Any?): Boolean = x is T

// A statement `when` mixes the readable tests with the named holes.
fun stmtWhenIs(a: Any?): Int {
    var r = 0
    when (a) {
        is Mode -> r = 1
        !is Int -> r = 3
        is java.util.Date -> r = 5
        else -> r = 4
    }
    return r
}
