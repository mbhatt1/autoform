// Not exported to Core: the oracle driver for cases.kt. Prints `name value` per case; a case
// that throws prints `name exception <class>`.
fun t(name: String, f: () -> Any?) {
    try { println(name + " " + f()) } catch (e: Throwable) { println(name + " exception " + e.javaClass.simpleName) }
}

fun main() {
    t("case_int_mul_wraps") { case_int_mul_wraps() }
    t("case_long_mul") { case_long_mul() }
    t("case_mixed_mul") { case_mixed_mul() }
    t("case_literal_is_long") { case_literal_is_long() }
    t("case_int_add_wraps") { case_int_add_wraps() }
    t("case_long_add_wraps") { case_long_add_wraps() }
    t("case_long_accumulate") { case_long_accumulate() }
    t("case_int_accumulate") { case_int_accumulate() }
    t("case_byte_incr") { case_byte_incr() }
    t("case_byte_plus_promotes") { case_byte_plus_promotes() }
    t("case_short_decr") { case_short_decr() }
    t("case_ubyte_incr") { case_ubyte_incr() }
    t("case_ubyte_plus_promotes") { case_ubyte_plus_promotes() }
    t("case_shl_masked_int") { case_shl_masked_int() }
    t("case_shl_masked_long") { case_shl_masked_long() }
    t("case_shl_long") { case_shl_long() }
    t("case_shr_int") { case_shr_int() }
    t("case_shr_long") { case_shr_long() }
    t("case_ushr_int") { case_ushr_int() }
    t("case_ushr_long") { case_ushr_long() }
    t("case_shr_assign_style") { case_shr_assign_style() }
    t("case_uint_sub_wraps") { case_uint_sub_wraps() }
    t("case_ulong_sub_wraps") { case_ulong_sub_wraps() }
    t("case_uint_mul_wraps") { case_uint_mul_wraps() }
    t("case_ulong_mul_wraps") { case_ulong_mul_wraps() }
    t("case_uint_div") { case_uint_div() }
    t("case_uint_rem") { case_uint_rem() }
    t("case_uint_shr") { case_uint_shr() }
    t("case_uint_shl_masked") { case_uint_shl_masked() }
    t("case_ulong_shr") { case_ulong_shr() }
    t("case_min_div") { case_min_div() }
    t("case_min_rem") { case_min_rem() }
    t("case_long_min_div") { case_long_min_div() }
    t("case_long_div") { case_long_div() }
    t("case_rem_sign") { case_rem_sign() }
    t("case_int_neg_min") { case_int_neg_min() }
    t("case_long_neg") { case_long_neg() }
    t("case_div_zero") { case_div_zero() }
    t("case_long_rem_zero") { case_long_rem_zero() }
    t("case_uint_div_zero") { case_uint_div_zero() }
    t("case_int_inv") { case_int_inv() }
    t("case_long_inv") { case_long_inv() }
    t("case_uint_inv") { case_uint_inv() }
    t("case_ubyte_inv") { case_ubyte_inv() }
    t("case_and_or_xor") { case_and_or_xor() }
    t("case_long_and") { case_long_and() }
    t("case_uint_xor") { case_uint_xor() }
    t("case_to_int_trunc") { case_to_int_trunc() }
    t("case_to_long_sign_extends") { case_to_long_sign_extends() }
    t("case_to_byte_trunc") { case_to_byte_trunc() }
    t("case_to_uint_reinterpret") { case_to_uint_reinterpret() }
    t("case_to_ulong_sign_extends") { case_to_ulong_sign_extends() }
    t("case_uint_to_int") { case_uint_to_int() }
    t("case_uint_to_long") { case_uint_to_long() }
    t("case_long_to_uint") { case_long_to_uint() }
    t("case_uint_gt") { case_uint_gt() }
    t("case_int_long_compare") { case_int_long_compare() }
    t("case_conditional") { case_conditional() }
    t("case_compound_int") { case_compound_int() }
    t("case_compound_long") { case_compound_long() }
    t("case_compound_uint") { case_compound_uint() }
}
