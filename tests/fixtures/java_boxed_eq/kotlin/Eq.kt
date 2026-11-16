fun nulIntEq(a: Int?, b: Int?): Boolean = a == b
fun nulIntNe(a: Int?, b: Int?): Boolean = a != b
fun nulLongEq(a: Long?, b: Long?): Boolean = a == b
fun nulBoolEq(a: Boolean?, b: Boolean?): Boolean = a == b
fun nulCharEq(a: Char?, b: Char?): Boolean = a == b
fun plainIntEq(a: Int, b: Int): Boolean = a == b
fun intLitEq(a: Int?): Boolean = a == 5
fun intLitNe(a: Int?): Boolean = a != 5
fun nullCheck(a: Int?): Boolean = a == null
fun nullCheckNe(a: Int?): Boolean = a != null
fun retNullable(x: Int): Int? = if (x > 0) x else null
fun localNullable(x: Int): Boolean { val a: Int? = retNullable(x); val b: Int? = 2; return a == b }
fun callEq(x: Int): Boolean { val a = retNullable(x); return a == 3 }
fun fromJava(b: java.lang.Integer?): Boolean = b == 5
fun boxCmp(b: java.lang.Integer?): Boolean = b == b
fun longLocal(x: Long): Boolean { val a: Long? = x; return a == x }
fun callCmp(x: Int): Boolean = retNullable(x) == retNullable(x)
fun refEqInt(a: Int?, b: Int?): Boolean = a === b
fun argEq(a: Int?, b: Int?): Boolean = kId(a == b)
fun kId(x: Boolean): Boolean = x
fun callRight(x: Int, a: Int?): Boolean = a == retNullable(x)
