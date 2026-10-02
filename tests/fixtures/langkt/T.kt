// The hand-written Kotlin control experiment behind ast-LangKt.json (docs/languages.md,
// "Kotlin (toy)"): the original source was never kept, this is its reconstruction from the
// committed AST (gcd and addAll, plus the file's module initializer). Item S re-exported
// the AST from THIS file so that it has a recorded source.
fun gcd(a: Int, b: Int): Int {
    var x = a
    var y = b
    while (y != 0) {
        val t = x % y
        x = y
        y = t
    }
    return x
}

fun addAll(n: Int): Int {
    var s = 0
    var i = 0
    while (i < n) {
        s = s + i
        i = i + 1
    }
    return s
}
