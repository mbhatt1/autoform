// Width-typed Kotlin integer arithmetic (item S). The `case_*` functions are exported by
// cartographer/export_ast.sc and pinned in Autoform/KotlinIntWidth.lean; Main.kt (not
// exported) prints each result so tests/test_kotlinintwidth_kotlin.py can compare the
// pins with a real Kotlin compiler's output. Kotlin: Int is 32 bits and Long 64; overflow
// wraps; Byte/Short operands promote to Int; UInt/ULong wrap at their width; `shl`/`shr`/
// `ushr` count is masked to 5/6 bits; `/` and `%` by zero throw ArithmeticException.

fun case_int_mul_wraps(): Int { val a = 100000; val b = 100000; return a * b }
fun case_long_mul(): Long { val a = 100000L; val b = 100000L; return a * b }
fun case_mixed_mul(): Long { val a = 3000000000L; val b = 2; return a * b }
fun case_literal_is_long(): Long { val a = 3000000000; return a * 2 }
fun case_int_add_wraps(): Int { var x = 2147483647; x = x + 1; return x }
fun case_long_add_wraps(): Long { var x = 9223372036854775807L; x = x + 1; return x }
fun case_long_accumulate(): Long { var s = 0L; var i = 0; while (i < 3) { s += 2000000000; i++ }; return s }
fun case_int_accumulate(): Int { var s = 0; var i = 0; while (i < 3) { s += 2000000000; i++ }; return s }
fun case_byte_incr(): Byte { var b: Byte = 127; b++; return b }
fun case_byte_plus_promotes(): Int { val a: Byte = 127; val b: Byte = 1; return a + b }
fun case_short_decr(): Short { var s: Short = -32768; s--; return s }
fun case_ubyte_incr(): UByte { var b: UByte = 255u; b++; return b }
fun case_ubyte_plus_promotes(): UInt { val a: UByte = 255u; val b: UByte = 255u; return a + b }
fun case_shl_masked_int(): Int { val x = 1; return x shl 33 }
fun case_shl_masked_long(): Long { val x = 1L; return x shl 65 }
fun case_shl_long(): Long { val x = 1L; return x shl 33 }
fun case_shr_int(): Int { val x = -16; return x shr 1 }
fun case_shr_long(): Long { val x = -4294967296L; return x shr 4 }
fun case_ushr_int(): Int { val x = -1; return x ushr 28 }
fun case_ushr_long(): Long { val x = -1L; return x ushr 60 }
fun case_shr_assign_style(): Int { var x = -16; x = x shr 2; return x }
fun case_uint_sub_wraps(): UInt { val a: UInt = 0u; return a - 1u }
fun case_ulong_sub_wraps(): ULong { val a: ULong = 0uL; return a - 1uL }
fun case_uint_mul_wraps(): UInt { val a: UInt = 65536u; return a * a }
fun case_ulong_mul_wraps(): ULong { val a: ULong = 18446744073709551615uL; return a * 2uL }
fun case_uint_div(): UInt { val a: UInt = 4294967295u; val b: UInt = 2u; return a / b }
fun case_uint_rem(): UInt { val a: UInt = 4294967295u; val b: UInt = 10u; return a % b }
fun case_uint_shr(): UInt { val a: UInt = 4294967295u; return a shr 1 }
fun case_uint_shl_masked(): UInt { val a: UInt = 1u; return a shl 33 }
fun case_ulong_shr(): ULong { val a: ULong = 18446744073709551615uL; return a shr 60 }
fun case_min_div(): Int { val m = -2147483647 - 1; val d = -1; return m / d }
fun case_min_rem(): Int { val m = -2147483647 - 1; val d = -1; return m % d }
fun case_long_min_div(): Long { val m = -9223372036854775807L - 1; val d = -1L; return m / d }
fun case_long_div(): Long { val d = -7000000000L; return d / 2 }
fun case_rem_sign(): Int { val a = -7; val b = 3; return a % b }
fun case_int_neg_min(): Int { val y = -2147483647 - 1; return -y }
fun case_long_neg(): Long { val y = 5L; return -y }
fun case_div_zero(): Int { val a = 1; val b = 0; return a / b }
fun case_long_rem_zero(): Long { val a = 1L; val b = 0L; return a % b }
fun case_uint_div_zero(): UInt { val a: UInt = 1u; val b: UInt = 0u; return a / b }
fun case_int_inv(): Int { val a = 5; return a.inv() }
fun case_long_inv(): Long { val a = 0L; return a.inv() }
fun case_uint_inv(): UInt { val a: UInt = 0u; return a.inv() }
fun case_ubyte_inv(): UByte { val a: UByte = 5u; return a.inv() }
fun case_and_or_xor(): Int { val a = 12; val b = 10; return (a and b) + (a or b) * 100 + (a xor b) * 10000 }
fun case_long_and(): Long { val a = -1L; val b = 4294967295L; return a and b }
fun case_uint_xor(): UInt { val a: UInt = 4294967295u; val b: UInt = 255u; return a xor b }
fun case_to_int_trunc(): Int { val x = 4294967297L; return x.toInt() }
fun case_to_long_sign_extends(): Long { val x = -5; return x.toLong() }
fun case_to_byte_trunc(): Byte { val x = 300; return x.toByte() }
fun case_to_uint_reinterpret(): UInt { val x = -1; return x.toUInt() }
fun case_to_ulong_sign_extends(): ULong { val x = -1; return x.toULong() }
fun case_uint_to_int(): Int { val x: UInt = 4294967295u; return x.toInt() }
fun case_uint_to_long(): Long { val x: UInt = 4294967295u; return x.toLong() }
fun case_long_to_uint(): UInt { val x = -1L; return x.toUInt() }
fun case_uint_gt(): Boolean { val a: UInt = 4294967295u; val b: UInt = 1u; return a > b }
fun case_int_long_compare(): Boolean { val a = 3000000000L; val b = 1; return a > b }
fun case_conditional(): Long { val a = 100000L; return if (a > 0) a * a else a }
fun case_compound_int(): Int { var x = 100; x += 5; x *= 2; x -= 1; x /= 3; x %= 7; x = x shl 29; return x }
fun case_compound_long(): Long { var x = 4611686018427387904L; x += x; x *= 2; x %= 1000; return x }
fun case_compound_uint(): UInt { var x: UInt = 4000000000u; x += 500000000u; x *= 3u; x %= 1000u; return x }
