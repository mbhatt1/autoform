// Width-typed Go integer arithmetic (item S). The `case_*` functions are exported by
// cartographer/export_ast.sc and pinned in Autoform/GoIntWidth.lean; main.go (not
// exported) prints each result so tests/test_gointwidth_go.py can compare the pins with
// the `go` toolchain. Spec: https://go.dev/ref/spec#Arithmetic_operators ("Integer
// overflow") and #Integer_overflow, #Operators (shifts), #Conversions.
package main

// A Go `int` is 64 bits on amd64/arm64 (the stated data model): Core's untyped 32-bit
// `*` used to give 1410065408 here (STRATEGY §29 item 5, §63 "Not done").
func case_int_mul() int { m := 100000; return m * m }
func case_int_add_wraps() int { x := 9223372036854775807; x = x + 1; return x }
func case_int32_mul_wraps() int32 { var a int32 = 100000; return a * a }
func case_int64_mul() int64 { var a int64 = 100000; return a * a }
func case_int8_add_wraps() int8 { var a int8 = 127; a = a + 1; return a }
func case_int8_incr() int8 { var a int8 = 127; a++; return a }
func case_int16_compound() int16 { var a int16 = 32767; a += 2; return a }
func case_uint8_sub_wraps() uint8 { var a uint8 = 0; a = a - 1; return a }
func case_byte_add_wraps() byte { var b byte = 200; return b + b }
func case_rune_add_wraps() rune { var r rune = 2147483647; return r + 1 }
func case_uint32_mul_wraps() uint32 { var a uint32 = 65536; return a * a }
func case_uint64_mul_wraps() uint64 { var a uint64 = 9223372036854775808; return a * 2 }
func case_uint64_sub_wraps() uint64 { var a uint64 = 0; return a - 1 }
func case_uint_sub_wraps() uint { var a uint = 0; return a - 1 }
func case_uintptr_sub_wraps() uintptr { var p uintptr = 0; return p - 1 }
func case_uint16_neg() uint16 { var a uint16 = 1; return -a }
func case_int_neg_min() int64 { var y int64 = -9223372036854775808; return -y }
func case_uint8_complement() uint8 { var x uint8 = 5; return ^x }
func case_int64_complement() int64 { var z int64 = 0; return ^z }
func case_and_not() uint8 { var x uint8 = 255; var y uint8 = 15; return x &^ y }
// MinInt / -1 is MinInt, MinInt % -1 is 0 in Go: no panic ("if the dividend x is the
// most negative value for the int type of x, the quotient q = x / -1 is equal to x").
func case_min_div() int64 { var m int64 = -9223372036854775808; var d int64 = -1; return m / d }
func case_min_rem() int64 { var m int64 = -9223372036854775808; var d int64 = -1; return m % d }
func case_int8_min_div() int8 { var m int8 = -128; var d int8 = -1; return m / d }
func case_div_trunc() int { var a int = -7; var b int = 2; return a / b }
func case_rem_sign() int { var a int = -7; var b int = 3; return a % b }
func case_uint32_div() uint32 { var a uint32 = 4294967295; var b uint32 = 2; return a / b }
// Shifts: a count >= the width gives 0 (or -1 for a negative signed `>>`), not a mask.
func case_shl_over_width() int32 { var x int32 = 1; var n uint = 33; return x << n }
func case_shl_in_width() int32 { var x int32 = 1; var n uint = 31; return x << n }
func case_shl_int64() int64 { var x int64 = 1; var n uint = 63; return x << n }
func case_shr_over_width_neg() int32 { var x int32 = -8; var n uint = 40; return x >> n }
func case_shr_over_width_pos() int32 { var x int32 = 8; var n uint = 40; return x >> n }
func case_shr_arith() int32 { var x int32 = -16; var n uint = 2; return x >> n }
func case_shr_uint() uint32 { var x uint32 = 4294967295; var n uint = 28; return x >> n }
func case_shl_count_type() uint8 { var x uint8 = 1; var n uint8 = 7; return x << n }
func case_shl_signed_count() int64 { var x int64 = 1; var n int = 62; return x << n }
func case_shl_drops_bits() uint8 { var x uint8 = 255; var n uint = 4; return x << n }
// Comparisons: unsigned compare is unsigned, no C-style conversion.
func case_uint32_gt() bool { var a uint32 = 4294967295; var b uint32 = 1; return a > b }
func case_int8_lt() bool { var a int8 = -1; var b int8 = 1; return a < b }
// Accumulation at `int` (64-bit): the old 32-bit loop wrapped at 2^32.
func case_int_accumulate() int {
	s := 0
	for i := 0; i < 3; i++ {
		s += 2000000000
		s *= 3
	}
	return s
}
// Conversions between integer types wrap (spec: Conversions between numeric types).
func case_conv_int32_trunc() int32 { var x int64 = 4294967297; return int32(x) }
func case_conv_uint8_trunc() uint8 { var x int = 300; return uint8(x) }
func case_conv_sign_extend() uint64 { var x int8 = -1; return uint64(x) }
func case_conv_int64_widen() int64 { var x int32 = -5; return int64(x) }
// A non-constant shift of an untyped constant takes its type from the context; the
// exporter cannot see that, so it is a hole (op:int:untyped-constant-shift).
func case_untyped_const_shift() int64 { var n uint = 40; return 1 << n }
// Package-level named integer types resolve to their underlying type (`Level` is uint8),
// an untyped named constant takes the type of its other operand (`mask` is 2^64-1, which
// no `int` holds; a package-level constant is a field access Core cannot read yet), a local whose initializer is a conversion has that type, and a constant
// expression is evaluated exactly.
type Level uint8

func case_named_type_wraps() Level { var l Level = 200; return l + 100 }
func case_untyped_const_operand() uint64 {
	const mask = 1<<64 - 1 // untyped, and no int holds it: gosrc2cpg still says `int`
	var x uint64 = 5
	return x ^ mask
}
func case_local_from_conversion() uint8 { var n int64 = 300; s := uint8(n); s = s + 250; return s }
func case_const_expr_exact() int64 { return 1<<40 + 7 }
func case_const_conversion() uint64 { return uint64(1<<64 - 1) }
// Compound assignment performs the operation at the target's type (`x op= y` is `x = x op y`).
func case_compound_ops() uint8 {
	var x uint8 = 100
	x += 200
	x *= 3
	x -= 7
	x /= 2
	x %= 50
	x |= 0x81
	x &= 0xF7
	x ^= 0x55
	x <<= 3
	x >>= 1
	return x
}
func case_compound_and_not() uint16 { var x uint16 = 0xFFFF; x &^= 0x0F0F; return x }
func case_compound_shl_count() int32 { var x int32 = 1; var n uint = 35; x <<= n; return x }
func case_compound_int64() int64 { var x int64 = 4611686018427387904; x += x; x *= 2; return x }
// Both of these panic at run time; Core: an exception, not a value.
func case_div_zero() int { var a int = 1; var b int = 0; return a / b }
func case_neg_shift() int64 { var x int64 = 1; var n int = -1; return x << n }
func case_rem_zero() uint8 { var a uint8 = 1; var b uint8 = 0; return a % b }
