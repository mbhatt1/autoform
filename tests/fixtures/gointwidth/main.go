// Not exported to Core: the oracle driver for cases.go. Prints `name value` per case;
// a case that panics prints `name panic: <runtime error>` (recovered here, which Core
// does not model, so this file stays out of the export).
package main

import (
	"fmt"
	"os"
)

func try(name string, f func() string) {
	defer func() {
		if r := recover(); r != nil {
			fmt.Printf("%s panic: %v\n", name, r)
		}
	}()
	fmt.Printf("%s %s\n", name, f())
}

func s(v any) string { return fmt.Sprint(v) }

func main() {
	cases := []struct {
		n string
		f func() string
	}{
		{"case_int_mul", func() string { return s(case_int_mul()) }},
		{"case_int_add_wraps", func() string { return s(case_int_add_wraps()) }},
		{"case_int32_mul_wraps", func() string { return s(case_int32_mul_wraps()) }},
		{"case_int64_mul", func() string { return s(case_int64_mul()) }},
		{"case_int8_add_wraps", func() string { return s(case_int8_add_wraps()) }},
		{"case_int8_incr", func() string { return s(case_int8_incr()) }},
		{"case_int16_compound", func() string { return s(case_int16_compound()) }},
		{"case_uint8_sub_wraps", func() string { return s(case_uint8_sub_wraps()) }},
		{"case_byte_add_wraps", func() string { return s(case_byte_add_wraps()) }},
		{"case_rune_add_wraps", func() string { return s(case_rune_add_wraps()) }},
		{"case_uint32_mul_wraps", func() string { return s(case_uint32_mul_wraps()) }},
		{"case_uint64_mul_wraps", func() string { return s(case_uint64_mul_wraps()) }},
		{"case_uint64_sub_wraps", func() string { return s(case_uint64_sub_wraps()) }},
		{"case_uint_sub_wraps", func() string { return s(case_uint_sub_wraps()) }},
		{"case_uintptr_sub_wraps", func() string { return s(case_uintptr_sub_wraps()) }},
		{"case_uint16_neg", func() string { return s(case_uint16_neg()) }},
		{"case_int_neg_min", func() string { return s(case_int_neg_min()) }},
		{"case_uint8_complement", func() string { return s(case_uint8_complement()) }},
		{"case_int64_complement", func() string { return s(case_int64_complement()) }},
		{"case_and_not", func() string { return s(case_and_not()) }},
		{"case_min_div", func() string { return s(case_min_div()) }},
		{"case_min_rem", func() string { return s(case_min_rem()) }},
		{"case_int8_min_div", func() string { return s(case_int8_min_div()) }},
		{"case_div_trunc", func() string { return s(case_div_trunc()) }},
		{"case_rem_sign", func() string { return s(case_rem_sign()) }},
		{"case_uint32_div", func() string { return s(case_uint32_div()) }},
		{"case_shl_over_width", func() string { return s(case_shl_over_width()) }},
		{"case_shl_in_width", func() string { return s(case_shl_in_width()) }},
		{"case_shl_int64", func() string { return s(case_shl_int64()) }},
		{"case_shr_over_width_neg", func() string { return s(case_shr_over_width_neg()) }},
		{"case_shr_over_width_pos", func() string { return s(case_shr_over_width_pos()) }},
		{"case_shr_arith", func() string { return s(case_shr_arith()) }},
		{"case_shr_uint", func() string { return s(case_shr_uint()) }},
		{"case_shl_count_type", func() string { return s(case_shl_count_type()) }},
		{"case_shl_signed_count", func() string { return s(case_shl_signed_count()) }},
		{"case_shl_drops_bits", func() string { return s(case_shl_drops_bits()) }},
		{"case_uint32_gt", func() string { return s(case_uint32_gt()) }},
		{"case_int8_lt", func() string { return s(case_int8_lt()) }},
		{"case_int_accumulate", func() string { return s(case_int_accumulate()) }},
		{"case_conv_int32_trunc", func() string { return s(case_conv_int32_trunc()) }},
		{"case_conv_uint8_trunc", func() string { return s(case_conv_uint8_trunc()) }},
		{"case_conv_sign_extend", func() string { return s(case_conv_sign_extend()) }},
		{"case_conv_int64_widen", func() string { return s(case_conv_int64_widen()) }},
		{"case_untyped_const_shift", func() string { return s(case_untyped_const_shift()) }},
		{"case_named_type_wraps", func() string { return s(case_named_type_wraps()) }},
		{"case_untyped_const_operand", func() string { return s(case_untyped_const_operand()) }},
		{"case_local_from_conversion", func() string { return s(case_local_from_conversion()) }},
		{"case_const_expr_exact", func() string { return s(case_const_expr_exact()) }},
		{"case_const_conversion", func() string { return s(case_const_conversion()) }},
		{"case_compound_ops", func() string { return s(case_compound_ops()) }},
		{"case_compound_and_not", func() string { return s(case_compound_and_not()) }},
		{"case_compound_shl_count", func() string { return s(case_compound_shl_count()) }},
		{"case_compound_int64", func() string { return s(case_compound_int64()) }},
		{"case_div_zero", func() string { return s(case_div_zero()) }},
		{"case_neg_shift", func() string { return s(case_neg_shift()) }},
		{"case_rem_zero", func() string { return s(case_rem_zero()) }},
	}
	for _, c := range cases {
		try(c.n, c.f)
	}
	_ = os.Args
}
