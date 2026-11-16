package s

object Calls {
    var n = 1
    fun one(by: Int): Int { n = n + by; return n }
    fun implicit(by: Int): Int = one(by) + 1
    fun explicit(by: Int): Int = this.one(by) + 1
}

class Counter(var n: Int = 3) {
    fun inc(by: Int): Int { n = n + by; return n }
    fun implicit(by: Int): Int = inc(by) * 2
    fun explicit(by: Int): Int = this.inc(by) * 2
    companion object {
        fun twice(x: Int): Int = x * 2
        fun implicit(x: Int): Int = twice(x) + 1
        fun explicit(x: Int): Int = this.twice(x) + 1
    }
}

enum class Mode { ON, OFF;
    fun isOn(): Boolean = this == ON
    fun implicit(): Boolean = !isOn()
    fun explicit(): Boolean = !this.isOn()
}
