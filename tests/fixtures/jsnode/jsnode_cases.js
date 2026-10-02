// JavaScript conformance cases for the Joern jssrc2cpg -> Core pipeline (item R).
//
// Every `case_*` function takes no arguments and returns a number, a boolean or a string.
// tests/test_jsnode_node.py loads this file's text with `new Function(...)`, runs every
// case under Node, and compares each result with what Core computes (pinned in
// Autoform/JsNode.lean) for the exporter's REAL output on this same file. The file must
// stay a list of plain function declarations: no top-level statements, no imports.
//
// What these cases are about: jssrc2cpg 4.0.606 erases `===`/`==`, `!==`/`!=` and
// `>>>`/`>>` (each pair becomes one operator), and lowers `a ?? b` to the operator of
// `a || b`. The exporter recovers the token from source text.

// ---- strict versus loose equality -------------------------------------------------
function case_strict_str_vs_num() { return 1 === "1"; }      // false
function case_loose_same_type() { return 2 == 2; }           // true
function case_strict_same_type() { return 2 === 2; }         // true
function case_strict_ne_cross() { return 1 !== "1"; }        // true
function case_loose_ne_same() { return 3 != 3; }             // false
function case_strict_ne_same() { return "a" !== "a"; }       // false
function case_strict_bool_vs_num() { return true === 1; }    // false
// jssrc2cpg re-quotes a string literal as "..." whatever the source used, so the operand
// text no longer matches the source text of the whole expression:
function case_single_quote_eq() { return 'a' === 'a'; }      // true
function case_single_quote_ne() { return 'a' !== 'b'; }      // true
function case_single_quote_cross() { return 'a' === "a"; }   // true
function case_strict_nan() { return NaN === NaN; }           // false
function case_nan_ne() { return NaN !== NaN; }               // true
function case_inf_strict() { return Infinity === Infinity; } // true
function case_inf_vs_big() { return Infinity > 1000000; }    // true
function case_strict_negzero() { return -0 === 0; }          // true
function case_strict_int_float() { return 1 === 1.0; }       // true

// ---- null and undefined ---------------------------------------------------------
function case_null_loose_zero() { return null == 0; }        // false
function case_zero_loose_null() { var z = 0; return z == null; }   // false
function case_empty_str_loose_null() { var s = ""; return s == null; }  // false
function case_false_loose_null() { var f = false; return f == null; }  // false
function case_null_loose_null() { var n = null; return n == null; }    // true
function case_undef_loose_null() { var u = undefined; return u == null; }          // true
function case_null_loose_undef() { return null == undefined; }         // true
function case_null_ne_zero() { var z = 0; return z != null; }          // true
function case_null_ne_null() { var n = null; return n != null; }       // false
function case_zero_strict_null() { var z = 0; return z === null; }     // false
function case_null_strict_null() { var n = null; return n === null; }  // true
function case_null_strict_undefined() { return null === undefined; }   // false
function case_undef_strict_undef() { var u = undefined; return u === undefined; }  // true
function case_null_strict_ne_undefined() { return null !== undefined; } // true

// ---- shifts ----------------------------------------------------------------------
function case_sar_neg() { return -1 >> 0; }                  // -1
function case_shr_neg() { return -1 >>> 0; }                 // 4294967295
function case_sar_neg16() { return -16 >> 2; }               // -4
function case_shr_neg16() { return -16 >>> 28; }             // 15
function case_shl_sign() { return 1 << 31; }                 // -2147483648
function case_shr_var() { var x = -2; return x >>> 1; }          // 2147483647
function case_sar_var_call() { var x = -2; return x >> 1; }  // -1

// ---- nullish coalescing: the left value survives unless it is null/undefined ------
function case_nullish_zero() { return 0 ?? 5; }              // 0
function case_nullish_empty() { return "" ?? "d"; }          // ""
function case_nullish_false() { return false ?? 5; }         // false
function case_nullish_null() { return null ?? 5; }           // 5
function case_nullish_undef() { var u = undefined; return u ?? 7; }      // 7
function case_nullish_chain() { var u = undefined; var n = null; return u ?? n ?? 3; }   // 3
function case_nullish_value() { return 9 ?? 5; }             // 9
function case_nullish_single_quote() { return '' ?? 'd'; }       // ""
function case_nullish_single_quote_null() { return null ?? 'd'; }   // d
function case_nullish_var_zero() { var a = 0; var b = 5; return a ?? b; }      // 0
function case_nullish_var_null() { var a = null; var b = 5; return a ?? b; }   // 5
function case_nullish_short_circuit() {
  var c = 0;
  var r = 1 ?? (c = 9);
  return c;                                                  // 0
}
function case_nullish_right_effect() {
  var c = 0;
  var r = null ?? (c = 9);
  return c + r;                                              // 18
}
function case_nullish_impure_left() {
  var c = 0;
  var r = c++ ?? 4;
  return r * 100 + c;                                        // 1
}
function case_nullish_in_cond() { var z = 0; return (z ?? 5) === 0; }        // true

// ---- the neighbours that must not change -----------------------------------------
function case_or_zero() { return 0 || 5; }                   // 5
function case_and_zero() { return 0 && 5; }                  // 0
function case_or_then_nullish() { var z = 0; return (z || 8) ?? 1; }          // 8
